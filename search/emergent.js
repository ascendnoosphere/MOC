"use strict";
// Dimension-emergent MOC search. See search/README.md.
function buildCore() {
  "use strict";
  const add=(a,b)=>[a[0]+b[0],a[1]+b[1]], sub=(a,b)=>[a[0]-b[0],a[1]-b[1]];
  const mul=(a,b)=>[a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]];
  const conj=a=>[a[0],-a[1]], dot=(a,b)=>a[0]*b[0]+a[1]*b[1], norm2=a=>dot(a,a);
  const abs=a=>Math.hypot(a[0],a[1]), scale=(a,t)=>[a[0]*t,a[1]*t];
  const div=(a,b)=>scale(mul(a,conj(b)),1/norm2(b));
  const zero=a=>a[0]===0&&a[1]===0, izero=a=>a[0]===0n&&a[1]===0n;
  const cmp=(a,b)=>a<b?-1:a>b?1:0;
  const cross=(o,a,b)=>(a[0]-o[0])*(b[1]-o[1])-(a[1]-o[1])*(b[0]-o[0]);
  class Exhausted extends Error { constructor(){super("oracle work budget exhausted");} }
  function meter(limit) {
    let used=0;
    return {tick(k=1){used+=k;if(used>limit)throw new Exhausted();},get used(){return used;}};
  }
  function hull(points) {
    points.sort((a,b)=>cmp(a[0],b[0])||cmp(a[1],b[1]));
    const p=points.filter((a,i)=>!i||a[0]!==points[i-1][0]||a[1]!==points[i-1][1]);
    if(p.length<3)return p;
    const chain=q=>{const s=[];for(const x of q){while(s.length>1&&cross(s[s.length-2],s[s.length-1],x)<=0)s.pop();s.push(x);}return s;};
    const l=chain(p),r=chain(p.slice().reverse());l.pop();r.pop();return l.concat(r);
  }
  // H(S) = conv union_{j in S} z[n-|S|,j] H(S\{j}).
  // Complex multiplication is real-linear, so discarding interior products is exact.
  function subsetHull(z,limit,{integer=false,paths=false,store=null}={}) {
    const n=z.length, full=(1n<<BigInt(n))-1n, m=meter(limit), cache=new Map();
    const one=integer?[1n,0n]:[1,0];if(paths)one.push(null);
    cache.set(0n,[one]);
    function rec(mask,i) {
      const old=cache.get(mask);if(old)return old;
      m.tick();const pts=[];
      // Cache by the actual remaining factor matrix, not dimension or mask.
      // Column labels in cached paths are local to the subproblem.
      // Exact verification deliberately does not consume external caches.
      let key=null,cols=null;
      if(store&&!integer&&paths&&n-i>=3){
        cols=[];for(let j=0;j<n;j++)if(mask&(1n<<BigInt(j)))cols.push(j);
        if(cols.length<=8||i===0){
          key="hull-v3:"+JSON.stringify(z.slice(i).map(row=>cols.map(j=>row[j])));
          const hit=store.get(key);
          if(hit!==undefined){m.tick(hit.length);const h=hit.map(([x,y,p])=>[x,y,p.reduceRight((q,j)=>[cols[j],q],null)]);cache.set(mask,h);return h;}
        }
      }
      for(let j=0;j<n;j++){
        const bit=1n<<BigInt(j);if(!(mask&bit))continue;
        const child=rec(mask^bit,i+1);m.tick(child.length);
        for(const p of child){const x=mul(z[i][j],p);if(paths)x.push([j,p[2]]);pts.push(x);}
      }
      const h=hull(pts);cache.set(mask,h);
      if(key&&h.every(p=>Number.isFinite(p[0])&&Number.isFinite(p[1])))store.set(key,h.map(p=>[p[0],p[1],unpack(p).map(j=>cols.indexOf(j))]));
      return h;
    }
    return {points:rec(full,0),work:m.used,states:cache.size};
  }
  function unpack(p){const r=[];for(let q=p[2];q;q=q[1])r.push(q[0]);return r;}
  function product(z,p,skip=-1,integer=false){
    let v=integer?[1n,0n]:[1,0];for(let i=0;i<p.length;i++)if(i!==skip)v=mul(v,z[i][p[i]]);return v;
  }
  function signedGap(h,d){
    let best=-Infinity,dir=[1,0],radius=0;
    for(const p of h)radius=Math.max(radius,abs(p));
    if(!h.length)return {gap:-Infinity,dir,radius:0};
    function test(p,v){const l=abs(v);if(!l)return;const e=scale(v,1/l),g=dot(e,sub(d,p));if(g>best){best=g;dir=e;}}
    if(h.length===1){const v=sub(d,h[0]);test(h[0],zero(v)?[1,0]:v);}
    else if(h.length===2){const v=sub(h[1],h[0]),w=[v[1],-v[0]];test(h[0],w);test(h[0],scale(w,-1));test(h[1],v);test(h[0],scale(v,-1));}
    else for(let i=0;i<h.length;i++){const p=h[i],v=sub(h[(i+1)%h.length],p);test(p,[v[1],-v[0]]);}
    // Outside a polygon, a nearest vertex may give a direction between two
    // facet normals. Use the Euclidean projection, not just facet distances.
    if(best>0&&h.length>1){
      let nearest=null,dist=Infinity;
      for(let i=0;i<h.length;i++){const p=h[i],v=sub(h[(i+1)%h.length],p),l=norm2(v);
        if(!l)continue;const t=Math.max(0,Math.min(1,dot(sub(d,p),v)/l)),q=add(p,scale(v,t)),dd=abs(sub(d,q));
        if(dd<dist){nearest=q;dist=dd;}}
      if(nearest&&dist>0){dir=scale(sub(d,nearest),1/dist);let support=-Infinity;for(const p of h)support=Math.max(support,dot(dir,p));best=dot(dir,d)-support;}
    }
    return {gap:best,dir,radius};
  }
  function rng(seed){
    let s=(seed>>>0)||0x9e3779b9;
    const r=()=>{s^=s<<13;s^=s>>>17;s^=s<<5;return (s>>>0)/4294967296;};
    r.int=n=>Math.floor(r()*n);r.normal=()=>Math.sqrt(-2*Math.log(Math.max(1e-15,r())))*Math.cos(2*Math.PI*r());
    r.point=()=>[r.normal(),r.normal()];return r;
  }
  function identity(n,integer=false){return Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>integer?[i===j?1n:0n,0n]:[i===j?1:0,0]));}
  function gate(q){const t=norm2(q),d=1+t;return [(1-t)/d,scale(q,2/d)];}
  function applyGate(U,g){
    const [i,j,x,y]=g,[c,s]=gate([x,y]),cs=conj(s);
    for(let k=0;k<U.length;k++){const a=U[i][k],b=U[j][k];U[i][k]=sub(scale(a,c),mul(cs,b));U[j][k]=add(mul(s,a),scale(b,c));}
  }
  function mixer(g){const U=identity(g.a.length);for(const e of g.gates)applyGate(U,e);return U;}
  function normal(U,b){
    const n=b.length, W=U.map(row=>row.map((v,j)=>mul(v,b[j])));
    return Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>{let s=[0,0];for(let k=0;k<n;k++)s=add(s,mul(W[i][k],conj(U[j][k])));return s;}));
  }
  function sumMatrix(a,b,U){
    const M=normal(U,b);for(let i=0;i<a.length;i++)M[i][i]=add(M[i][i],a[i]);return M;
  }
  function detInv(A,wantInverse=false){
    const n=A.length,M=A.map(r=>r.slice()),I=wantInverse?identity(n):null;let d=[1,0];
    for(let k=0;k<n;k++){
      let p=k;for(let i=k+1;i<n;i++)if(norm2(M[i][k])>norm2(M[p][k]))p=i;
      if(zero(M[p][k])||!Number.isFinite(norm2(M[p][k])))return {det:[0,0],inv:null};
      if(p!==k){[M[p],M[k]]=[M[k],M[p]];if(I)[I[p],I[k]]=[I[k],I[p]];d=scale(d,-1);}
      const v=M[k][k];d=mul(d,v);
      if(I){
        for(let j=k;j<n;j++)M[k][j]=div(M[k][j],v);
        for(let j=0;j<n;j++)I[k][j]=div(I[k][j],v);
        for(let i=0;i<n;i++)if(i!==k){const f=M[i][k];if(zero(f))continue;for(let j=k;j<n;j++)M[i][j]=sub(M[i][j],mul(f,M[k][j]));for(let j=0;j<n;j++)I[i][j]=sub(I[i][j],mul(f,I[k][j]));}
      }else{
        for(let i=k+1;i<n;i++){const f=div(M[i][k],v);for(let j=k+1;j<n;j++)M[i][j]=sub(M[i][j],mul(f,M[k][j]));}
      }
    }
    return {det:d,inv:I};
  }
  function determinant(M,rows){return detInv(rows?M.map((r,i)=>r.map(v=>scale(v,1/rows[i]))):M).det;}
  // Exact maximizer on a two-row SU(2) orbit, modulo floating arithmetic.
  // With K=(A+B)^-1 and delta=a_j-a_i:
  // D(G)/D = 1+t T+Re(c*s) X+Im(c*s) Y.
  function orbitGate(g,E,i,j){
    const {det:d,inv:K}=E.inverse||(E.inverse=detInv(E.M,true));
    if(!K||!(abs(d)>0)||!Number.isFinite(abs(d)))return null;
    const da=sub(g.a[j],g.a[i]),kd=sub(mul(K[i][i],K[j][j]),mul(K[i][j],K[j][i]));
    const T=sub(mul(da,sub(K[i][i],K[j][j])),mul(mul(da,da),kd));
    const X=mul(da,add(K[i][j],K[j][i])),Y=mul([0,1],mul(da,sub(K[i][j],K[j][i])));
    const u=scale(d,1/abs(d)),p=dot(E.dir,mul(u,T)),x=dot(E.dir,mul(u,X)),y=dot(E.dir,mul(u,Y));
    const L=Math.hypot(p,x,y);if(!(L>1e-14)||!Number.isFinite(L))return null;
    const t=Math.max(0,Math.min(1,(1+p/L)/2)),c=Math.sqrt(1-t),xy=Math.hypot(x,y);
    const s=xy?scale([x,y],Math.sqrt(t)/xy):[Math.sqrt(t),0],q=scale(s,1/(1+c));
    return [i,j,q[0],q[1]];
  }
  // Remove redundant gates by unitary QR. The discarded right diagonal phases
  // commute with diag(b), so the represented normal matrix is unchanged.
  function compact(U){
    const n=U.length,W=U.map(r=>r.slice()),out=[];
    for(let j=0;j<n;j++)for(let i=n-1;i>j;i--){
      const x=W[j][j],y=W[i][j],ax=abs(x),ay=abs(y);if(ay<1e-15)continue;
      const h=Math.hypot(ax,ay),c=ax/h,s=ax?scale(div(y,x),-c):[1,0],q=scale(s,1/(1+c));
      applyGate(W,[j,i,q[0],q[1]]);out.push([j,i,-q[0],-q[1]]);
    }
    return out.reverse();
  }
  function shuffle(n,r){const p=Array.from({length:n},(_,i)=>i);for(let i=n-1;i>0;i--){const j=r.int(i+1);[p[i],p[j]]=[p[j],p[i]];}return p;}
  function factors(a,b){
    const rows=[],z=a.map(x=>{const p=b.map(y=>add(x,y)),s=4*Math.max(1,abs(x));rows.push(s);return p.map(v=>scale(v,1/s));});
    return {rows,z};
  }
  function sampled(z,r,count){
    const n=z.length,ps=[],keys=new Set();
    function put(p){const k=p.join(",");if(!keys.has(k)){keys.add(k);ps.push(p.slice());}}
    put(Array.from({length:n},(_,i)=>i));put(Array.from({length:n},(_,i)=>n-i-1));
    for(let k=0;k<count;k++)put(shuffle(n,r));
    // Directional two-swap ascent supplies better inner-hull vertices.
    for(let k=0;k<8;k++){
      const angle=k*Math.PI/4,e=[Math.cos(angle),Math.sin(angle)],p=shuffle(n,r);
      let v=product(z,p);
      for(let pass=0;pass<2;pass++){
        let gain=false;
        for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){
          const old=mul(z[i][p[i]],z[j][p[j]]);let w;
          if(norm2(old)>1e-24)w=mul(div(v,old),mul(z[i][p[j]],z[j][p[i]]));
          else{[p[i],p[j]]=[p[j],p[i]];w=product(z,p);[p[i],p[j]]=[p[j],p[i]];}
          if(dot(e,w)>dot(e,v)+1e-15){[p[i],p[j]]=[p[j],p[i]];v=product(z,p);gain=true;}
        }
        if(!gain)break;
      }
      put(p);
    }
    return ps;
  }
  function cacheSpectra(g,r,o){
    const f=factors(g.a,g.b),ps=sampled(f.z,r,o.samples),sp=ps.map(p=>product(f.z,p));
    return {...f,a:g.a,b:g.b,ps,sp,inner:hull(sp.slice()),full:null,attempted:false};
  }
  function evaluate(g,parent,r,o){
    const n=g.a.length;
    let U,M;
    const same=parent&&parent.g.a===g.a&&parent.g.b===g.b;
    if(same&&g.gates.length===parent.g.gates.length+1&&parent.g.gates.every((x,i)=>x===g.gates[i])){
      // Incremental G B G*: two row/column updates instead of rebuilding B.
      const e=g.gates[g.gates.length-1],[i,j,x,y]=e,[c,t]=gate([x,y]);
      U=parent.U.map(row=>row.slice());applyGate(U,e);
      M=parent.M.map(row=>row.slice());
      for(let k=0;k<n;k++)M[k][k]=sub(M[k][k],g.a[k]);
      applyGate(M,e);
      for(let k=0;k<n;k++){const v=M[k][i],w=M[k][j];M[k][i]=sub(scale(v,c),mul(t,w));M[k][j]=add(mul(conj(t),v),scale(w,c));}
      for(let k=0;k<n;k++)M[k][k]=add(M[k][k],g.a[k]);
    }else{
      U=parent&&parent.g.gates===g.gates?parent.U:mixer(g);M=sumMatrix(g.a,g.b,U);
    }
    const C=same?parent.C:cacheSpectra(g,r,o);
    const matrixKey=o.cache?"det-v3:"+JSON.stringify([g.a,g.b,g.gates]):null;
    let D=matrixKey?o.cache.get(matrixKey):undefined;
    if(D===undefined){D=determinant(M,C.rows);if(matrixKey&&D.every(Number.isFinite))o.cache.set(matrixKey,D);}
    const s=signedGap(C.inner,D);
    // Inner hull gives an optimistic upper bound on signed directional gap.
    // Spend the expensive oracle on near-boundary spectra, not every random point.
    let oracleWork=0,oracleExhausted=0;
    if(!C.attempted&&(s.gap>-.15*Math.max(s.radius,1e-100)||r()<.12)){
      C.attempted=true;
      try{C.full=subsetHull(C.z,o.work,{paths:true,store:o.cache});oracleWork=C.full.work;}catch(e){if(!(e instanceof Exhausted))throw e;oracleWork=o.work;oracleExhausted=1;}
    }
    const H=C.full?C.full.points:C.inner,G=signedGap(H,D);
    const relative=G.gap/Math.max(G.radius,1e-100),mix=1-U.reduce((s,row)=>s+Math.max(...row.map(norm2)),0)/n;
    let h=-Infinity;for(const p of H)h=Math.max(h,dot(G.dir,p));
    let near=0;for(const p of C.sp)if(h-dot(G.dir,p)<.025*Math.max(G.radius,1e-100))near++;
    const contactBonus=Math.min(1,near/Math.max(1,2*n-1));
    // Near contacts are heuristic only; no exact count or pruning follows.
    // A balanced terminal witness has a nonnormal sum. Do not make
    // this a hard numerical constraint; use it to discourage commuting limits.
    let comm=0,energy=0;
    for(let i=0;i<n;i++)for(let j=0;j<n;j++){energy+=norm2(M[i][j]);if(i!==j){const da=sub(g.a[i],g.a[j]);comm+=norm2(sub(mul(da,conj(M[j][i])),mul(conj(da),M[i][j])));}}
    const nonnormal=Math.sqrt(comm)/Math.max(energy,1e-100);
    const score=(C.full?Math.max(-2,relative):Math.min(0,Math.max(-2,relative))-.08)+.025*mix+.004*contactBonus+.018*nonnormal;
    const descriptor=[Math.log1p(n),Math.min(2,g.gates.length/(n*(n-1)/2)),mix,nonnormal,contactBonus];
    return {g,C,U,M,D,dir:G.dir,gap:relative,score,mix,near,nonnormal,descriptor,complete:!!C.full,oracleWork,oracleExhausted};
  }
  function normalize(g){
    const n=g.a.length;if(!n)return g;
    let t=[0,0];for(let i=0;i<n;i++)t=add(t,sub(g.a[i],g.b[i]));t=scale(t,1/(2*n));
    const a=g.a.map(x=>sub(x,t)),b=g.b.map(x=>add(x,t));
    const s=Math.sqrt((a.reduce((s,x)=>s+norm2(x),0)+b.reduce((s,x)=>s+norm2(x),0))/(2*n))||1;
    return {...g,a:a.map(x=>scale(x,1/s)),b:b.map(x=>scale(x,1/s))};
  }
  // Avoid global renormalization on every local edit: it destroys exact
  // cache keys for unchanged spectral subproblems. Normalize only on drift.
  function stabilize(g){return g.a.concat(g.b).some(x=>abs(x)>8)?normalize(g):g;}
  function pair(n,r){let i=r.int(n),j=r.int(n-1);if(j>=i)j++;return i<j?[i,j]:[j,i];}
  function randomGate(i,j,r,step=.8){return [i,j,r.normal()*step,r.normal()*step];}
  function spectralPair(mode,r){
    let a=r.point(),b=r.point();
    if(mode===1)b=add(scale(a,-1),scale(r.point(),.18));
    if(mode===2){a=[a[0],(r()<.5?-1:1)*.45+.06*a[1]];b=[b[0],(r()<.5?-1:1)*.45+.06*b[1]];}
    if(mode===3){a=[a[0],(r()<.18?1:.015)*a[1]];b=[b[0],(r()<.18?1:.015)*b[1]];}
    if(mode===4){a=add([(r()<.5?-1:1),0],scale(a,.25));b=add([(r()<.5?-1:1),0],scale(b,.25));}
    return [a,b];
  }
  function birth(g,r){
    const n=g.a.length,[a,b]=spectralPair(g.mode,r),gates=g.gates.map(([i,j,x,y])=>[i+1,j+1,x,y]);
    // Prepend the new label: unchanged suffix subproblems survive growth.
    if(n){const links=1+r.int(Math.min(n,3));for(let k=0;k<links;k++)gates.splice(r.int(gates.length+1),0,randomGate(0,1+r.int(n),r));}
    return stabilize({...g,a:[a,...g.a],b:[b,...g.b],gates});
  }
  function death(g,r){
    const n=g.a.length,j=r.int(n),keep=(x,i)=>i!==j;
    return stabilize({...g,a:g.a.filter(keep),b:g.b.filter(keep),gates:g.gates.filter(e=>e[0]!==j&&e[1]!==j).map(e=>[e[0]-(e[0]>j),e[1]-(e[1]>j),e[2],e[3]])});
  }
  function components(g){
    const n=g.a.length,seen=new Set(),adj=Array.from({length:n},()=>[]),out=[];
    for(const [i,j,x,y] of g.gates)if(x!==0||y!==0){adj[i].push(j);adj[j].push(i);}
    for(let k=0;k<n;k++)if(!seen.has(k)){const q=[k];seen.add(k);for(let i=0;i<q.length;i++)for(const j of adj[q[i]])if(!seen.has(j)){seen.add(j);q.push(j);}out.push(q.sort((a,b)=>a-b));}
    return out;
  }
  function reduceBlocks(g,r){
    const cs=components(g);if(cs.length===1)return g;
    const viable=cs.filter(c=>c.length>=4);if(!viable.length)return null;
    const c=viable[r.int(viable.length)],map=new Map(c.map((k,i)=>[k,i]));
    return stabilize({...g,a:c.map(i=>g.a[i]),b:c.map(i=>g.b[i]),gates:g.gates.filter(e=>map.has(e[0])&&map.has(e[1])).map(e=>[map.get(e[0]),map.get(e[1]),e[2],e[3]])});
  }
  function allowed(g){
    const n=g.a.length;
    if(n<4||components(g).length!==1)return false;
    const distinct=a=>new Set(a.map(x=>x.join(","))).size,da=distinct(g.a),db=distinct(g.b);
    if(da<=2||db<=2||(da<=3&&db<=3))return false;
    // Checked opposite-pair multiplicity theorem. Exact equality only;
    // numerical near-coincidence is deliberately not excluded.
    const count=(xs,z)=>xs.filter(x=>x[0]===z[0]&&x[1]===z[1]).length;
    for(const a of g.a)for(const b of g.b)if(zero(add(a,b))&&(n===4||count(g.a,a)+count(g.b,b)>=n-2))return false;
    return true;
  }
  function restart(r){
    let g={a:[],b:[],gates:[],mode:r.int(8)};
    // Grow a graph from no labels. The only lower bound is the checked n<=3 theorem.
    do{g=birth(g,r);}while(g.a.length<4||r()<.58);
    const n=g.a.length;
    for(let k=0;k<n;k++){const [i,j]=pair(n,r);g.gates.push(randomGate(i,j,r));}
    if(g.mode===5){
      // Open all-order family: two Householder reflections.
      let U=identity(n);
      for(let k=0;k<2;k++){
        let v=Array.from({length:n},()=>r.point());const l=Math.sqrt(v.reduce((a,x)=>a+norm2(x),0));v=v.map(x=>scale(x,1/l));
        const w=Array.from({length:n},(_,j)=>{let s=[0,0];for(let i=0;i<n;i++)s=add(s,mul(conj(v[i]),U[i][j]));return s;});
        U=U.map((row,i)=>row.map((x,j)=>sub(x,scale(mul(v[i],w[j]),2))));
      }
      g.gates=compact(U);
    }else if(g.mode===6){
      // Open Fourier family in arbitrary order; no order is selected for it.
      const U=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>{const t=2*Math.PI*i*j/n;return [Math.cos(t)/Math.sqrt(n),Math.sin(t)/Math.sqrt(n)];}));
      g.gates=compact(U);
    }else if(g.mode===7)g.gates=g.gates.map(e=>[e[0],e[1],e[2],0]);
    return g;
  }
  function clip(poly,line,h){
    if(!poly.length)return poly;const out=[],f=p=>line[0]*p[0]+line[1]*p[1]+line[2]-h;
    for(let i=0;i<poly.length;i++){const p=poly[i],q=poly[(i+1)%poly.length],a=f(p),b=f(q);
      if(a>=0)out.push(p);if((a>=0)!==(b>=0)){const t=a/(a-b);out.push(add(p,scale(sub(q,p),t)));}}
    return out;
  }
  function maxMin(lines,step){
    let lo=Infinity,hi=Infinity;
    for(const [a,b,c] of lines){lo=Math.min(lo,c);hi=Math.min(hi,c+step*(Math.abs(a)+Math.abs(b)));}
    let point=[0,0];if(!Number.isFinite(lo)||!Number.isFinite(hi))return point;
    for(let i=0;i<24;i++){
      const h=(lo+hi)/2;let p=[[-step,-step],[step,-step],[step,step],[-step,step]];
      for(const l of lines){p=clip(p,l,h);if(!p.length)break;}
      if(p.length){lo=h;point=scale(p.reduce(add,[0,0]),1/p.length);}else hi=h;
    }
    return point;
  }
  // For one free spectral entry the determinant and all matching products
  // are affine. Optimize the lower envelope of active constraints in a box.
  // This is a proposal oracle, not a separation certificate.
  function freeEntry(E,r,step,o){
    const g=E.g,C=E.C,n=g.a.length,side=r()<.5?"a":"b",i=r.int(n);
    const a=g.a.slice(),b=g.b.slice(),v=side==="a"?a:b;v[i]=add(v[i],[1,0]);
    const dd=sub(determinant(sumMatrix(a,b,E.U),C.rows),E.D);
    const ps=C.ps.slice();if(C.full)for(const p of C.full.points)ps.push(unpack(p));
    const lines=[],keys=new Set();
    function constraint(p){
      const key=p.join(",");if(keys.has(key))return false;keys.add(key);
      const k=side==="a"?i:p.indexOf(i),P=product(C.z,p),dp=scale(product(C.z,p,k),1/C.rows[k]),s=sub(dd,dp);
      lines.push([dot(E.dir,s),dot(E.dir,mul([0,1],s)),dot(E.dir,sub(E.D,P))]);return true;
    }
    for(const p of ps)constraint(p);
    let d=maxMin(lines,step);
    // At most two violated-contact additions. Each oracle uses the old
    // positive row scales, so the affine model and support use identical units.
    if(E.complete&&E.gap>-.15)for(let pass=0;pass<2;pass++){
      const z=C.z.map((row,k)=>row.map((x,j)=>(side==="a"?k===i:j===i)?add(x,scale(d,1/C.rows[k])):x));
      try{
        const h=subsetHull(z,Math.max(1,Math.floor(o.work/2)),{paths:true,store:o.cache}).points;
        let contact=h[0];for(const p of h)if(dot(E.dir,p)>dot(E.dir,contact))contact=p;
        const actual=dot(E.dir,sub(add(E.D,mul(dd,d)),contact)),predicted=Math.min(...lines.map(l=>l[0]*d[0]+l[1]*d[1]+l[2]));
        if(predicted-actual<=1e-10*Math.max(1,Math.abs(predicted))||!constraint(unpack(contact)))break;
        d=maxMin(lines,step);
      }catch(e){if(!(e instanceof Exhausted))throw e;break;}
    }
    v[i]=add(g[side][i],d);
    return stabilize({...g,a,b});
  }
  // Numerical chart for the equal-e1/e2 reduction: solve the rational
  // moment equation for a regular reciprocal pole. Failure is harmless.
  function balancedPole(g,r){
    const n=g.a.length,one=[1,0],c=g.b.map(x=>scale(x,-1));
    let p=scale(r.point(),1.5);
    function moments(list,p){
      let s=[0,0],t=[0,0],u=[0,0],mass=0;
      for(const z of list){const den=sub(p,z);if(abs(den)<1e-5)return null;const x=div(one,den),x2=mul(x,x);s=add(s,x);t=add(t,x2);u=add(u,mul(x2,x));mass+=norm2(x);}
      return {s,t,u,mass};
    }
    for(let k=0;k<30;k++){
      if(abs(p)>10)return null;
      const x=moments(g.a,p),y=moments(c,p);if(!x||!y)return null;
      const F=sub(scale(sub(x.t,y.t),n),sub(mul(x.s,x.s),mul(y.s,y.s)));
      const denom=n*(x.mass+y.mass)+norm2(x.s)+norm2(y.s);
      if(abs(F)<1e-10*denom){
        const out=normalize({...g,a:g.a.map(z=>div(one,sub(p,z))),b:c.map(z=>scale(div(one,sub(p,z)),-1))});
        const sum2=a=>a.reduce((s,x)=>add(s,mul(x,x)),[0,0]);
        if(abs(sub(sum2(out.a),sum2(out.b)))<1e-6*n)return out;
        return null;
      }
      const Fp=scale(sub(sub(mul(x.s,x.t),mul(y.s,y.t)),scale(sub(x.u,y.u),n)),2);
      if(abs(Fp)<1e-15)return null;let d=div(F,Fp);if(abs(d)>1)d=scale(d,1/abs(d));p=sub(p,d);
    }
    return null;
  }
  function projective(g,r){
    if(r()<.5){const balanced=balancedPole(g,r);if(balanced)return balanced;}
    const t=scale(r.point(),.25),one=[1,0];
    const fa=x=>div(x,add(one,mul(t,x))),fb=x=>div(x,sub(one,mul(t,x)));
    if(g.a.some(x=>abs(add(one,mul(t,x)))<.2)||g.b.some(x=>abs(sub(one,mul(t,x)))<.2))return g;
    return normalize({...g,a:g.a.map(fa),b:g.b.map(fb)});
  }
  function solveReal(A,b){
    const n=b.length,M=A.map((r,i)=>r.concat(b[i]));
    for(let k=0;k<n;k++){
      let p=k;for(let i=k+1;i<n;i++)if(Math.abs(M[i][k])>Math.abs(M[p][k]))p=i;
      if(Math.abs(M[p][k])<1e-20)return null;[M[p],M[k]]=[M[k],M[p]];
      for(let i=k+1;i<n;i++){const v=M[i][k]/M[k][k];for(let j=k+1;j<=n;j++)M[i][j]-=v*M[k][j];}
    }
    const x=Array(n).fill(0);for(let i=n-1;i>=0;i--){let v=M[i][n];for(let j=i+1;j<n;j++)v-=M[i][j]*x[j];x[i]=v/M[i][i];}return x;
  }
  function productDerivatives(C,p){
    const n=p.length,pre=[[1,0]],suf=Array(n+1);suf[n]=[1,0];
    for(let i=0;i<n;i++)pre.push(mul(pre[i],C.z[i][p[i]]));
    for(let i=n-1;i>=0;i--)suf[i]=mul(C.z[i][p[i]],suf[i+1]);
    const grad=Array(2*n);
    for(let i=0;i<n;i++){const d=scale(mul(pre[i],suf[i+1]),1/C.rows[i]);grad[i]=d;grad[n+p[i]]=d;}
    return {p:pre[n],grad};
  }
  // Terminal-contact proposal: linearize the 2n-1 top contact equalities
  // while preserving the complex D-P_pivot to first order. This is a
  // regularized numerical continuation step, not the exact transfer theorem.
  function contactStep(E,r,step){
    const {g,C,U,dir}=E,n=g.a.length,ps=[],keys=new Set();
    function addPerm(p){const key=p.join(",");if(keys.has(key))return;keys.add(key);const z=product(C.z,p);ps.push({p,z,h:dot(dir,z)});}
    for(const p of C.ps)addPerm(p);
    if(C.full)for(const p of C.full.points)addPerm(unpack(p));
    ps.sort((a,b)=>b.h-a.h);
    const seeds=ps.slice(0,4);
    for(const {p} of seeds)for(let i=0;i<n;i++)for(let j=i+1;j<n;j++){const q=p.slice();[q[i],q[j]]=[q[j],q[i]];addPerm(q);}
    ps.sort((a,b)=>b.h-a.h);
    const pivot=productDerivatives(C,ps[0].p),R=Math.max(abs(pivot.p),abs(E.D),1e-100),rows=[],rhs=[];
    const realRow=(grad,e)=>grad.flatMap(v=>[dot(e,v)/R,dot(e,mul([0,1],v))/R]);
    for(const {p} of ps.slice(1,2*n-1)){
      const z=productDerivatives(C,p),delta=z.grad.map((v,i)=>sub(v,pivot.grad[i]));
      rows.push(realRow(delta,dir));rhs.push(-dot(dir,sub(z.p,pivot.p))/R);
    }
    const inv=E.inverse||(E.inverse=detInv(E.M,true)),K=inv.inv;
    if(K){
      const dg=Array(2*n);
      for(let i=0;i<n;i++)dg[i]=mul(E.D,K[i][i]);
      for(let j=0;j<n;j++){
        let z=[0,0];
        for(let i=0;i<n;i++)for(let k=0;k<n;k++)z=add(z,mul(conj(U[i][j]),mul(K[i][k],U[k][j])));
        dg[n+j]=mul(E.D,z);
      }
      const d=dg.map((v,i)=>sub(v,pivot.grad[i]));
      rows.push(realRow(d,[1,0]).map(x=>1.5*x),realRow(d,[0,1]).map(x=>1.5*x));rhs.push(0,0);
    }
    if(!rows.length)return g;
    const inner=(a,b)=>a.reduce((s,x,i)=>s+x*b[i],0);
    const A=rows.map(a=>rows.map(b=>inner(a,b))),trace=A.reduce((s,row,i)=>s+row[i],0),lambda=Math.max(1e-10,trace/rows.length*1e-5);
    for(let i=0;i<A.length;i++)A[i][i]+=lambda;
    const y=solveReal(A,rhs);if(!y)return g;
    const d=Array.from({length:4*n},(_,j)=>rows.reduce((s,row,i)=>s+y[i]*row[j],0));
    let m=0;for(let j=0;j<2*n;j++)m=Math.max(m,Math.hypot(d[2*j],d[2*j+1]));
    if(!Number.isFinite(m)||m<1e-13)return g;
    const t=Math.min(1,step/m),a=g.a.map((v,i)=>add(v,[t*d[2*i],t*d[2*i+1]])),b=g.b.map((v,i)=>add(v,[t*d[2*(n+i)],t*d[2*(n+i)+1]]));
    return stabilize({...g,a,b});
  }
  function mutate(E,r,o){
    const g=E.g,n=g.a.length,u=r(),step=Math.exp(-3.3+3*r());
    if(u<.17){let child=birth(g,r);while(r()<.12)child=birth(child,r);return child;}
    if(u<.28)return death(g,r);
    if(u<.48){const [i,j]=pair(n,r),e=orbitGate(g,E,i,j)||randomGate(i,j,r,step);return {...g,gates:g.gates.concat([e])};}
    if(u<.61)return freeEntry(E,r,step,o);
    if(u<.71)return contactStep(E,r,step);
    if(u<.77)return projective(g,r);
    if(u<.88){
      const gates=g.gates.slice();
      if(gates.length&&r()<.65){const i=r.int(gates.length),e=gates[i];if(r()<.20)gates.splice(i,1);else gates[i]=[e[0],e[1],e[2]+step*r.normal(),e[3]+step*r.normal()];}
      else{const [i,j]=pair(n,r);gates.splice(r.int(gates.length+1),0,randomGate(i,j,r,step));}
      return {...g,gates};
    }
    const a=g.a.slice(),b=g.b.slice(),s=r()<.5?a:b,i=r.int(n);
    s[i]=add(s[i],scale(r.point(),step));
    if(r()<.25){const j=r.int(n);s[j]=add(s[j],scale(r.point(),step));}
    return stabilize({...g,a,b});
  }
  function exactDivide(a,b){
    const p=mul(a,conj(b)),d=norm2(b);
    if(d===0n||p[0]%d!==0n||p[1]%d!==0n)throw new Error("non-exact Gaussian division");
    return [p[0]/d,p[1]/d];
  }
  function bareiss(A){
    const n=A.length,M=A.map(r=>r.slice());let prev=[1n,0n],sign=1n;
    if(!n)return prev;
    for(let k=0;k<n-1;k++){
      let p=k;while(p<n&&izero(M[p][k]))p++;if(p===n)return [0n,0n];
      if(p!==k){[M[p],M[k]]=[M[k],M[p]];sign=-sign;}
      const d=M[k][k];for(let i=k+1;i<n;i++)for(let j=k+1;j<n;j++)M[i][j]=exactDivide(sub(mul(d,M[i][j]),mul(M[i][k],M[k][j])),prev);
      for(let i=k+1;i<n;i++)M[i][k]=[0n,0n];prev=d;
    }
    return scale(M[n-1][n-1],sign);
  }
  function exactMixer(n,gates){
    const V=identity(n,true);let q=1n;
    for(const [i,j,X,Y,Q] of gates){
      if(!Number.isInteger(i)||!Number.isInteger(j)||i<0||j>=n||i>=j||Q<=0n)throw new Error("invalid rational gate");
      const t=X*X+Y*Y,d=Q*Q+t,c=Q*Q-t,s=[2n*Q*X,2n*Q*Y];
      for(let k=0;k<n;k++){const a=V[i][k],b=V[j][k];V[i][k]=sub(scale(a,c),mul(conj(s),b));V[j][k]=add(mul(s,a),scale(b,c));}
      for(let l=0;l<n;l++)if(l!==i&&l!==j)for(let k=0;k<n;k++)V[l][k]=scale(V[l][k],d);
      q*=d;
    }
    // Independent arithmetic check of unitarity, not a floating tolerance.
    for(let i=0;i<n;i++)for(let j=0;j<n;j++){
      let v=[0n,0n];for(let k=0;k<n;k++)v=add(v,mul(V[i][k],conj(V[j][k])));
      if(v[0]!==(i===j?q*q:0n)||v[1]!==0n)throw new Error("exact unitarity check failed");
    }
    return {V,q};
  }
  function integerMatrix(a,b,V,q){
    const n=a.length,W=V.map(r=>r.map((v,j)=>mul(v,b[j])));
    return Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>{
      let s=i===j?scale(a[i],q*q):[0n,0n];for(let k=0;k<n;k++)s=add(s,mul(W[i][k],conj(V[j][k])));return s;
    }));
  }
  // A branch can be discarded only if its complete-product disk lies strictly
  // below the requested integer threshold. Row maxima relax injectivity safely.
  function diskSeparate(z,e,target,den,limit){
    const n=z.length,m=meter(limit),sq=z.map(r=>r.map(norm2)),e2=norm2(e),d2=den*den,T2=target*target;
    let pruned=0,leaves=0;
    // Scalar max-product assignment DP is much cheaper than polygon DP.
    // Use it when its transition count fits the budget; otherwise use a
    // cached independent-row relaxation. Both are exact upper bounds.
    const full=(1n<<BigInt(n))-1n,exactMod=target>0n&&BigInt(n)*(full+1n)<=BigInt(Math.floor(limit/3)),bounds=new Map([[0n,1n]]);
    function tailBound(mask,i){
      const old=bounds.get(mask);if(old!==undefined)return old;
      let v=exactMod?0n:1n;
      if(exactMod){
        for(let j=0;j<n;j++)if(mask&(1n<<BigInt(j))){m.tick();const x=sq[i][j]*tailBound(mask^(1n<<BigInt(j)),i+1);if(x>v)v=x;}
      }else{
        for(let k=i;k<n;k++){let max=0n;for(let j=0;j<n;j++)if((mask&(1n<<BigInt(j)))&&sq[k][j]>max)max=sq[k][j];v*=max;m.tick(n);}
      }
      bounds.set(mask,v);return v;
    }
    function rec(mask,i,p){
      m.tick();if(i===n){leaves++;return dot(e,p)*den<target;}
      if(target>0n){
        const bound=norm2(p)*e2*d2*tailBound(mask,i);
        if(bound<T2){pruned++;return true;}
      }
      const js=[];for(let j=0;j<n;j++)if(mask&(1n<<BigInt(j)))js.push(j);
      js.sort((j,k)=>cmp(sq[i][k],sq[i][j]));
      for(const j of js)if(!rec(mask^(1n<<BigInt(j)),i+1,mul(p,z[i][j])))return false;
      return true;
    }
    return {strict:rec(full,0,[1n,0n]),work:m.used,pruned,leaves,exactModulusAssignment:exactMod};
  }
  function rationalize(E,Q){
    const q=x=>String(BigInt(Math.round(x*Q))),v=x=>x.map(q);
    return {format:"moc-emergent-v1",a:E.g.a.map(v),b:E.g.b.map(v),direction:v(E.dir),
      gates:compact(E.U).map(([i,j,x,y])=>[i,j,q(x),q(y),String(Q)])};
  }
  function verify(cert,limit=1000000,discoverDirection=false){
    if(cert.format!=="moc-emergent-v1")throw new Error("unknown certificate format");
    const cv=v=>{if(!Array.isArray(v)||v.length!==2||v.some(x=>typeof x!=="string"||!/^[-]?\d+$/.test(x)))throw new Error("invalid integer pair");return v.map(BigInt);};
    const a=cert.a.map(cv),b=cert.b.map(cv),e=cv(cert.direction),n=a.length;
    if(n!==b.length||!n||izero(e))throw new Error("invalid spectra or direction");
    const gates=cert.gates.map(g=>{if(g.length!==5||g.slice(2).some(x=>typeof x!=="string"||!/^[-]?\d+$/.test(x)))throw new Error("invalid gate");return [g[0],g[1],...g.slice(2).map(BigInt)];});
    const {V,q}=exactMixer(n,gates),D=bareiss(integerMatrix(a,b,V,q)),den=q**BigInt(2*n),target=dot(e,D);
    const z=a.map(x=>b.map(y=>add(x,y)));
    const result={dimension:n,determinantNumerator:D.map(String),denominator:String(den),projectedNumerator:String(target)};
    try{
      const H=subsetHull(z,limit,{integer:true});
      const support=e=>H.points.map(p=>dot(e,p)).reduce((x,y)=>x>y?x:y);
      let direction=e,max=support(e),projected=target,gap=projected-den*max;
      // If rounding spoiled the proposed direction, derive an integer
      // separating normal directly from the exact polygon and rational D.
      if(discoverDirection&&gap<=0n){
        const p=H.points,dirs=[];
        if(p.length===1)dirs.push(sub(D,scale(p[0],den)));
        else if(p.length===2){const v=sub(p[1],p[0]),w=[v[1],-v[0]];dirs.push(w,scale(w,-1n),v,scale(v,-1n));}
        else for(let i=0;i<p.length;i++){const v=sub(p[(i+1)%p.length],p[i]);dirs.push([v[1],-v[0]]);}
        for(const v of dirs){if(izero(v))continue;const m=support(v),d=dot(v,D),g=d-den*m;if(g>0n){direction=v;max=m;projected=d;gap=g;break;}}
      }
      return {...result,direction:direction.map(String),projectedNumerator:String(projected),status:gap>0n?"CERTIFIED":"NOT_SEPARATED",method:"exact-subset-hull",maximumMatchingProjection:String(max),gapNumerator:String(gap),work:H.work,states:H.states};
    }catch(err){if(!(err instanceof Exhausted))throw err;}
    try{
      const B=diskSeparate(z,e,target,den,limit);
      return {...result,direction:e.map(String),status:B.strict?"CERTIFIED":"NOT_SEPARATED",method:"exact-disk-branch-bound",...B};
    }catch(err){if(!(err instanceof Exhausted))throw err;return {...result,status:"INCONCLUSIVE",method:"budget-exhausted"};}
  }
  function search(options={},progress=()=>{}){
    const o={seed:1,steps:1000,population:24,work:80000,exactWork:1000000,samples:40,reportEvery:100,...options};
    const r=rng(o.seed),pool=[],dims={},stats={evaluated:0,rejected:0,complete:0,oracleWork:0,oracleExhausted:0,exactAttempts:0,exactInconclusive:0},best={gap:null,dimension:null},start=Date.now();
    const dist=(a,b)=>Math.sqrt(a.descriptor.reduce((s,x,i)=>s+(x-b.descriptor[i])**2,0));
    // One global quality-diversity population; no order-indexed subsearches.
    const novelty=(a,list)=>Math.min(...list.filter(x=>x!==a).map(x=>dist(a,x)),1);
    function fitness(a){return a.score+.08*novelty(a,pool);}
    function insert(E){
      if(pool.length<o.population){pool.push(E);return;}
      const route=r();
      if(route<.12){pool[r.int(pool.length)]=E;return;}
      if(route<.38){
        // Protect a structural frontier even when large new graphs start
        // with poor gaps. This uses continuous novelty, never order buckets.
        let crowded=0;for(let i=1;i<pool.length;i++)if(novelty(pool[i],pool)<novelty(pool[crowded],pool))crowded=i;
        if(novelty(E,pool)>novelty(pool[crowded],pool))pool[crowded]=E;
        return;
      }
      if(route<.70){
        let nearest=0;for(let i=1;i<pool.length;i++)if(dist(E,pool[i])<dist(E,pool[nearest]))nearest=i;
        if(dist(E,pool[nearest])<.18){if(E.score>=pool[nearest].score)pool[nearest]=E;return;}
      }
      let worst=0;for(let i=1;i<pool.length;i++)if(fitness(pool[i])<fitness(pool[worst]))worst=i;
      if(E.score+.08*novelty(E,pool)>fitness(pool[worst]))pool[worst]=E;
    }
    function snapshot(step){return {step,seed:o.seed,elapsedMs:Date.now()-start,dimensions:{...dims},...stats,best:{...best}};}
    // Import migrants from other workers or an earlier checkpoint.
    for(const x of (o.frontier||[]).slice(0,o.population)){
      const g=x.g;if(!g||!allowed(g)||g.a.length**3>o.work*16)continue;
      const E=evaluate(g,null,r,o);if(Number.isFinite(E.score)&&Number.isFinite(E.gap))insert(E);
    }
    function frontier(){return pool.map(E=>({g:E.g,score:E.score,descriptor:E.descriptor,gap:E.gap,complete:E.complete}));}
    for(let k=0;k<o.steps;k++){
      let parent=null,g;
      if(!pool.length||r()<.12)g=restart(r);
      else{
        parent=pool[r.int(pool.length)];
        const route=r(),metric=route<.26?x=>novelty(x,pool):fitness;
        if(route<.78)for(let i=0;i<2;i++){const x=pool[r.int(pool.length)];if(metric(x)>metric(parent))parent=x;}
        g=mutate(parent,r,o);
      }
      // The size guard is an operation budget, not a fixed order or order sweep.
      g=reduceBlocks(g,r);if(!g){stats.rejected++;continue;}
      const n=g.a.length;if(!allowed(g)||n*n*n>o.work*16){stats.rejected++;continue;}
      if(g.gates.length>2*n*n){g={...g,gates:compact(mixer(g))};}
      const E=evaluate(g,parent,r,o);if(!Number.isFinite(E.score)||!Number.isFinite(E.gap)){stats.rejected++;continue;}
      stats.evaluated++;dims[n]=(dims[n]||0)+1;stats.oracleWork+=E.oracleWork;stats.oracleExhausted+=E.oracleExhausted;
      if(E.complete){stats.complete++;if(best.gap===null||E.gap>best.gap){best.gap=E.gap;best.dimension=n;}}
      const tolerance=Math.max(1e-12,64*Number.EPSILON*n*n);
      if(E.gap>tolerance&&(E.complete||k%64===0)){
        stats.exactAttempts++;
        for(const Q of [10000,1000000,100000000,10000000000]){
          const cert=rationalize(E,Q),proof=verify(cert,o.exactWork,true);
          if(proof.status==="CERTIFIED")return {status:"CERTIFIED",certificate:{...cert,direction:proof.direction,proof},stats:snapshot(k+1)};
          if(proof.status==="INCONCLUSIVE"){stats.exactInconclusive++;break;}
        }
      }
      insert(E);
      if(o.reportEvery&&(k+1)%o.reportEvery===0)progress(snapshot(k+1));
    }
    return {status:"NO_CERTIFIED_COUNTEREXAMPLE",stats:snapshot(o.steps),...(o.returnFrontier?{frontier:frontier()}: {})};
  }
  function selftest(){
    const assert=(x,m)=>{if(!x)throw new Error("selftest: "+m);};
    const r=rng(73);let tests=0;
    function permutations(n){const out=[];function f(p,s){if(p.length===n){out.push(p);return;}for(let i=0;i<n;i++)if(!s.has(i))f(p.concat(i),new Set([...s,i]));}f([],new Set());return out;}
    for(let n=1;n<=6;n++)for(let rep=0;rep<3;rep++){
      const a=Array.from({length:n},()=>[BigInt(r.int(7)-3),BigInt(r.int(7)-3)]),b=Array.from({length:n},()=>[BigInt(r.int(7)-3),BigInt(r.int(7)-3)]);
      const z=a.map(x=>b.map(y=>add(x,y))),all=permutations(n).map(p=>product(z,p,-1,true)),H=subsetHull(z,1000000,{integer:true,paths:true});
      for(const p of H.points)assert(norm2(sub(p,product(z,unpack(p),-1,true)))===0n,"hull path");
      for(let k=0;k<12;k++){
        const e=[BigInt(r.int(9)-4),BigInt(r.int(9)-4)],max=p=>p.map(x=>dot(e,x)).reduce((a,b)=>a>b?a:b);
        assert(max(all)===max(H.points),"exact hull versus permutations");
        const h=max(all);assert(diskSeparate(z,e,h+1n,1n,1000000).strict,"disk strict");assert(!diskSeparate(z,e,h,1n,1000000).strict,"disk equality rejection");tests+=3;
      }
    }
    // Independent Leibniz determinant cross-check, including pivot swaps.
    for(let n=2;n<=5;n++)for(let k=0;k<4;k++){
      const A=Array.from({length:n},()=>Array.from({length:n},()=>[BigInt(r.int(5)-2),BigInt(r.int(5)-2)]));
      if(k===0)A[0][0]=[0n,0n];
      let d=[0n,0n];for(const p of permutations(n)){let parity=0;for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)parity^=Number(p[i]>p[j]);d=add(d,scale(product(A,p,-1,true),parity?-1n:1n));}
      assert(norm2(sub(d,bareiss(A)))===0n,"Bareiss versus Leibniz");tests++;
    }
    const z=[[2n,1n],[3n,-2n]],w=[[1n,4n],[-1n,1n]];
    assert(norm2(sub(bareiss([z,w]),sub(mul(z[0],w[1]),mul(z[1],w[0]))))===0n,"Bareiss determinant");tests++;
    for(let k=0;k<25;k++){
      const g=restart(r),U=mixer(g),M=sumMatrix(g.a,g.b,U),dir=r.point(),[i,j]=pair(g.a.length,r),D=determinant(M);
      const e=orbitGate(g,{M,dir},i,j);
      if(e){const U1=U.map(r=>r.slice());applyGate(U1,e);const v=dot(dir,determinant(sumMatrix(g.a,g.b,U1)));
        assert(v>=dot(dir,D)-1e-7*Math.max(1,abs(D)),"orbit ascent");
        for(let q=0;q<10;q++){const V=U.map(r=>r.slice());applyGate(V,randomGate(i,j,r));const h=dot(dir,determinant(sumMatrix(g.a,g.b,V)));assert(v>=h-1e-7*Math.max(1,Math.abs(v),Math.abs(h)),"orbit optimum");}tests+=11;}
      const V=mixer({...g,gates:compact(U)}),N=sumMatrix(g.a,g.b,V);
      for(let i=0;i<M.length;i++)for(let j=0;j<M.length;j++)assert(abs(sub(M[i][j],N[i][j]))<1e-9,"QR gate compression");tests++;
    }
    // Gap must be the true support distance, including vertex-normal cases.
    const h=hull([[0,0],[1,0],[1,1],[0,1]]),q=signedGap(h,[2,2]);
    assert(Math.abs(q.gap-Math.sqrt(2))<1e-12,"vertex distance");tests++;
    assert(Math.abs(signedGap(h,[.5,.5]).gap+.5)<1e-12,"interior distance");tests++;
    for(let k=0;k<10;k++){
      const g=restart(r),o={samples:12,work:10000},E=evaluate(g,null,r,o),[i,j]=pair(g.a.length,r),g2={...g,gates:g.gates.concat([randomGate(i,j,r)])},F=evaluate(g2,E,r,o),M=sumMatrix(g2.a,g2.b,mixer(g2));
      for(let i=0;i<M.length;i++)for(let j=0;j<M.length;j++)assert(abs(sub(F.M[i][j],M[i][j]))<1e-9,"incremental orbit update");tests++;
    }
    for(let k=0;k<8;k++){
      const g=restart(r),E=evaluate(g,null,r,{samples:20,work:10000}),p=E.C.ps[0],v=productDerivatives(E.C,p);
      const j=r.int(g.a.length),Z=E.C.z.map(row=>row.slice()),eps=1e-6;Z[j]=Z[j].map(x=>add(x,[eps/E.C.rows[j],0]));
      assert(abs(sub(scale(sub(product(Z,p),v.p),1/eps),v.grad[j]))<1e-7,"contact derivative");tests++;
      const h=contactStep(E,r,.1);assert(h.a.length===g.a.length&&h.a.every(x=>x.every(Number.isFinite)),"contact continuation");tests++;
    }
    const cert={format:"moc-emergent-v1",a:[["1","2"],["2","0"]],b:[["3","1"],["-1","4"]],gates:[],direction:["1","0"]};
    assert(verify(cert).status==="NOT_SEPARATED","identity not violation");tests++;
    cert.gates=[[0,1,"2","3","7"]];assert(verify(cert).status==="NOT_SEPARATED","two-order rational rotation");tests++;
    const sm=search({steps:70,seed:41,work:12000,exactWork:10000,reportEvery:0,samples:12});
    assert(Object.keys(sm.stats.dimensions).length>1,"mixed-order smoke run");tests++;
    const store=new Map(),base=[[[2,1],[3,0],[1,2]],[[1,-1],[3,1],[2,0]],[[2,2],[0,1],[4,0]]];
    subsetHull(base,100000,{paths:true,store});let hits=0;
    const shared={get(k){const v=store.get(k);if(v!==undefined)hits++;return v;},set(k,v){store.set(k,v);}};
    const grown=[[[3,1],[1,0],[2,1],[4,1]],...base.map((row,i)=>[[i+1,1],...row])];
    const x=subsetHull(grown,100000,{paths:true,store:shared}),y=subsetHull(grown,100000,{paths:true});
    assert(hits>0&&JSON.stringify(x.points.map(p=>p.slice(0,2)))===JSON.stringify(y.points.map(p=>p.slice(0,2))),"cross-order cache reuse");tests++;
    for(const p of x.points)assert(abs(sub(p,product(grown,unpack(p))))<1e-10,"cached path remapping");tests++;
    return {status:"PASS",assertions:tests,smoke:sm.stats,crossOrderCacheHits:hits};
  }
  return {search,verify,selftest,subsetHull,determinant,mixer,sumMatrix,gapFromPoints:(p,d)=>signedGap(hull(p.slice()),d)};
}

if (require.main === module) {
  const fs=require("node:fs");
  const {Worker,isMainThread,parentPort,workerData}=require("node:worker_threads");
  const core=buildCore();
  function args(v) {
    const o={}; for(let i=0;i<v.length;i+=2) {
      if(!v[i].startsWith("--")||i+1>=v.length)throw new Error("expected --option value");
      const k=v[i].slice(2);if(!["steps","seed","work","exact-work","population","samples","report-every","workers","out"].includes(k))throw new Error("unknown option "+k);
      const x=v[i+1];if(k==="out"){o.out=x;continue;}
      const n=Number(x);if(!Number.isSafeInteger(n)||n<0||(!n&&!["seed","report-every"].includes(k)))throw new Error("invalid "+k);
      o[k.replace(/-([a-z])/g,(_,c)=>c.toUpperCase())]=n;
    } return o;
  }
  function print(x){process.stdout.write(JSON.stringify(x)+"\n");}
  function finish(r,out){
    if(r.status==="CERTIFIED"){const p=out||"moc-counterexample.json";fs.writeFileSync(p,JSON.stringify(r.certificate,null,2)+"\n");print({status:r.status,certificate:p,proof:r.certificate.proof,stats:r.stats});}
    else print(r);
  }
  if(!isMainThread){
    const r=core.search(workerData,x=>parentPort.postMessage({progress:x}));parentPort.postMessage({result:r});
  } else try{
    const [cmd="search",...rest]=process.argv.slice(2);
    if(cmd==="selftest"){print(core.selftest());}
    else if(cmd==="verify"){if(!rest.length)throw new Error("verify requires a certificate path");const o=args(rest.slice(1));const r=core.verify(JSON.parse(fs.readFileSync(rest[0],"utf8")),o.work||1000000);print(r);process.exitCode=r.status==="CERTIFIED"?0:r.status==="INCONCLUSIVE"?2:1;}
    else if(cmd==="search"){
      const o=args(rest),workers=o.workers||1;
      if(workers===1)finish(core.search(o,x=>print({progress:x})),o.out);
      else{
        const ws=[],results=[];let done=false,remaining=workers;
        for(let i=0;i<workers;i++){
          const w=new Worker(__filename,{workerData:{...o,seed:((o.seed??1)+Math.imul(i,0x9e3779b9))>>>0}});ws.push(w);
          w.on("message",m=>{
            if(done)return;
            if(m.progress)print({worker:i,progress:m.progress});
            else if(m.result){
              results.push(m.result);remaining--;
              if(m.result.status==="CERTIFIED"){done=true;finish(m.result,o.out);for(const other of ws)other.terminate();}
              else if(!remaining){done=true;print({status:"NO_CERTIFIED_COUNTEREXAMPLE",workers:results.map(x=>x.stats)});}
            }
          });
          w.on("error",e=>{if(!done){done=true;console.error(e);process.exitCode=2;for(const other of ws)other.terminate();}});
          w.on("exit",code=>{if(!done&&code!==0){done=true;process.exitCode=2;console.error("worker exit",code);for(const other of ws)other.terminate();}});
        }
      }
    }else throw new Error("commands: search, verify, selftest");
  }catch(e){console.error(e.message);process.exitCode=2;}
}
module.exports=buildCore();
