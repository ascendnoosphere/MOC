"use strict";
// Arbitrary-size run-length two-layer cyclic unitary search.
function buildCyclic(core){
  "use strict";
  const C=(x=0,y=0)=>[x,y], add=(a,b)=>[a[0]+b[0],a[1]+b[1]], sub=(a,b)=>[a[0]-b[0],a[1]-b[1]], mul=(a,b)=>[a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]], sc=(a,t)=>[a[0]*t,a[1]*t], cj=a=>[a[0],-a[1]];
  const abs=a=>Math.hypot(a[0],a[1]), min=(a,b)=>a<b?a:b;
  const Z=[0,0,"0"], O=[1,0,"0"];
  // Scaled complex arithmetic: value=(x+iy)*2^exponent. The exponent is
  // an arbitrary-size integer; never convert a multiplicity to Number.
  function norm(a,e=0n){
    const m=Math.max(Math.abs(a[0]),Math.abs(a[1]));
    if(m===0)return Z;
    if(!Number.isFinite(m))throw Error("nonfinite scaled mantissa");
    let k=Math.floor(Math.log2(m));k=Math.max(-1022,Math.min(1023,k));
    return [a[0]/2**k,a[1]/2**k,String(e+BigInt(k))];
  }
  const zero=x=>x[0]===0&&x[1]===0;
  function times(a,b){if(zero(a)||zero(b))return Z;return norm(mul(a,b),BigInt(a[2])+BigInt(b[2]));}
  function plus(a,b){
    if(zero(a))return b;if(zero(b))return a;
    if(BigInt(a[2])<BigInt(b[2]))[a,b]=[b,a];
    const d=BigInt(a[2])-BigInt(b[2]);if(d>60n)return a;
    return norm(add(a,sc(b,2**(-Number(d)))),BigInt(a[2]));
  }
  const neg=a=>[-a[0],-a[1],a[2]], I=[O,Z,Z,O];
  const mm=(a,b)=>[plus(times(a[0],b[0]),times(a[1],b[2])),plus(times(a[0],b[1]),times(a[1],b[3])),plus(times(a[2],b[0]),times(a[3],b[2])),plus(times(a[2],b[1]),times(a[3],b[3]))];
  function power(base,n,one,op,store,kind){
    let out=one,bit=0,x=base;const key=store?"cycle-power-v1:"+kind+":"+JSON.stringify(base)+":":null;
    while(n>0n){
      if(bit>0){const k=key&&key+bit,hit=k?store.get(k):undefined;if(hit!==undefined)x=hit;else{x=op(x,x);if(k)store.set(k,x);}}
      if(n&1n)out=op(x,out);n>>=1n;bit++;
    }
    return out;
  }
  const cp=(a,n,s)=>power(a,n,O,times,s,"scalar"), mp=(a,n,s)=>power(a,n,I,mm,s,"matrix");
  function rotation([x,y,q]){const d=q*q+x*x+y*y;return [(q*q-x*x-y*y)/d,[2*q*x/d,2*q*y/d]];}
  // H diag(x,y) H*, or H* diag(x,y) H when inverse=true.
  function block(x,y,g,inverse=false){
    let [c,s]=rotation(g);if(inverse)s=sc(s,-1);
    const t=s[0]**2+s[1]**2,d=sub(x,y);
    return {l:add(sc(x,c*c),sc(y,t)),r:add(sc(x,t),sc(y,c*c)),u:sc(mul(cj(s),d),c),v:sc(mul(s,d),c)};
  }
  function cell(prev,t,next){
    const B=block(t.b[0],t.b[1],t.p),L=block(prev.a[1],t.a[0],prev.q,true),R=block(t.a[1],next.a[0],t.q,true);
    const transfer=(d,w)=>[norm(d),norm(sc(w,-1)),O,Z];
    const A=transfer(add(B.l,L.r),mul(L.u,L.v)),F=transfer(add(B.r,R.l),mul(B.u,B.v));
    return {T:mm(F,A),u:norm(mul(B.u,R.u)),v:norm(mul(B.v,R.v))};
  }
  function dimension(g){return 2n*g.runs.reduce((s,r)=>s+BigInt(r.count),0n);}
  function validate(g){
    if(!g||g.format!=="moc-cycle-rle-v1"||!Array.isArray(g.runs)||!g.runs.length)throw Error("invalid cyclic genome");
    for(const r of g.runs){
      if(typeof r.count!=="string"||!/^[1-9]\d*$/.test(r.count))throw Error("invalid run count");
      for(const x of [r.a,r.b])if(!Array.isArray(x)||x.length!==2||x.some(y=>!Array.isArray(y)||y.length!==2||y.some(z=>!Number.isSafeInteger(z)||Math.abs(z)>1000000)))throw Error("invalid spectrum");
      for(const x of [r.p,r.q])if(!Array.isArray(x)||x.length!==3||x.some(y=>!Number.isSafeInteger(y)||Math.abs(y)>1000000)||x[2]<=0)throw Error("invalid gate");
    }
    if(dimension(g)<4n)throw Error("cycle needs at least four labels");
    return g;
  }
  // In the basis of the second layer, A+B is cyclic tridiagonal.
  // The trace of the transfer product counts monomer/dimer matchings;
  // the two oriented full cycles have sign -1 in even dimension.
  function determinant(g,store){
    validate(g);
    const key=store?"cycle-det-v1:"+JSON.stringify(g.runs):null,hit=key?store.get(key):undefined;if(hit!==undefined)return hit;
    let T=I,u=O,v=O;const a=g.runs,r=a.length;
    function append(x,n){if(!n)return;T=mm(mp(x.T,n,store),T);u=times(cp(x.u,n,store),u);v=times(cp(x.v,n,store),v);}
    for(let j=0;j<r;j++){
      const t=a[j],p=a[(j+r-1)%r],q=a[(j+1)%r],n=BigInt(t.count);
      if(n===1n)append(cell(p,t,q),1n);
      else{append(cell(p,t,t),1n);if(n>2n)append(cell(t,t,t),n-2n);append(cell(t,t,q),1n);}
    }
    const d=plus(plus(T[0],T[3]),neg(plus(u,v)));if(key)store.set(key,d);return d;
  }
  function rng(seed){let s=(seed>>>0)||0x9e3779b9;const r=()=>{s^=s<<13;s^=s>>>17;s^=s<<5;return (s>>>0)/4294967296;};r.int=n=>Math.floor(r()*n);return r;}
  function stableSeed(s){let h=2166136261;for(let i=0;i<s.length;i++)h=Math.imul(h^s.charCodeAt(i),16777619);return h>>>0;}
  function shuffled(n,r){const a=Array.from({length:n},(_,i)=>i);for(let j=n-1;j>0;j--){const k=r.int(j+1);[a[j],a[k]]=[a[k],a[j]];}return a;}
  function types(g,side){
    const m=new Map();for(const t of g.runs)for(const z of t[side]){
      const k=JSON.stringify(z),v=m.get(k)||{z,count:0n};v.count+=BigInt(t.count);m.set(k,v);
    }return [...m.values()];
  }
  // Feasible type transportation tables are actual permutations, even
  // when their integer multiplicities are much larger than machine words.
  function matchSamples(g,samples,store){
    const A=types(g,"a"),B=types(g,"b"),m=A.length,n=B.length,z=A.map(a=>B.map(b=>norm(add(a.z,b.z))));
    const r=rng(stableSeed(JSON.stringify(g.runs))),out=[];
    let d=O;for(const t of g.runs)for(let j=0;j<2;j++)d=times(d,cp(norm(add(t.a[j],t.b[j])),BigInt(t.count),store));out.push(d);
    function transport(edges){
      const a=A.map(t=>t.count),b=B.map(t=>t.count);let p=O;
      for(const [i,j] of edges){const k=min(a[i],b[j]);if(k>0n){p=times(p,cp(z[i][j],k,store));a[i]-=k;b[j]-=k;}}
      if(a.some(x=>x!==0n)||b.some(x=>x!==0n))throw Error("incomplete transportation sample");
      return p;
    }
    const all=[];for(let i=0;i<m;i++)for(let j=0;j<n;j++)all.push([i,j]);
    const weight=([i,j])=>{const v=z[i][j];return zero(v)?-Infinity:Number(v[2])+Math.log2(abs(v));};
    out.push(transport(all.slice().sort((a,b)=>weight(b)-weight(a))));
    for(let k=0;k<samples;k++){
      const ai=shuffled(m,r),bj=shuffled(n,r),edges=[];
      for(const i of ai)for(const j of bj)edges.push([i,j]);
      // Every edge is still considered, hence each greedy transportation
      // fills exactly the prescribed row and column multiplicities.
      if(k%3===0)for(let i=edges.length-1;i>0;i--){const j=r.int(i+1);[edges[i],edges[j]]=[edges[j],edges[i]];}
      out.push(transport(edges));
    }
    return out;
  }
  function relative(x,reference){
    if(zero(x))return [0,0];const d=BigInt(x[2])-reference;
    if(d<-1070n)return [0,0];return sc(x,2**Number(d>100n?100n:d));
  }
  function evaluate(g,o={}){
    const samples=o.cycleSamples??12,store=o.cache,key=store?"cycle-eval-v2:"+samples+":"+JSON.stringify(g.runs):null,hit=key?store.get(key):undefined;if(hit!==undefined)return hit;
    const n=dimension(validate(g)),d=determinant(g,store),p=matchSamples(g,samples,store);
    const nz=p.filter(x=>!zero(x));const ref=nz.length?nz.map(x=>BigInt(x[2])).reduce((x,y)=>x>y?x:y):BigInt(d[2]);
    const G=core.gapFromPoints(p.map(x=>relative(x,ref)),relative(d,ref));
    const gap=G.gap/Math.max(G.radius,1e-100),logOrder=n.toString(2).length;
    const out={dimension:String(n),runs:g.runs.length,gap:Number.isFinite(gap)?gap:null,dir:G.dir,determinant:d,
      // Never interpret this as an exact support gap. Matching samples
      // form only an inner hull; accumulated floating phase error is unbounded.
      status:"UNRESOLVED_NUMERICAL",score:Math.max(-1,Math.min(0,Number.isFinite(gap)?gap:0))+.06*Math.tanh(Math.log1p(logOrder)/4)+.02*Math.log1p(g.runs.length),logOrder};
    if(key)store.set(key,out);return out;
  }
  function randomType(r){
    const v=()=>[r.int(9)-4,r.int(9)-4],g=()=>{let x=r.int(9)-4,y=r.int(9)-4;if(!x&&!y)x=1;return [x,y,1+r.int(7)];};
    return {count:"1",a:[v(),v()],b:[v(),v()],p:g(),q:g()};
  }
  function restart(r){return {format:"moc-cycle-rle-v1",runs:[randomType(r),randomType(r)]};}
  function mutate(g,r){
    const runs=g.runs.slice(),j=r.int(runs.length),t=runs[j],n=BigInt(t.count),u=r();
    if(u<.32){
      // Heavy-tailed multiplicative growth; no target dimension.
      const bits=r()<.15?9+r.int(48):1+r.int(8);
      runs[j]={...t,count:String((n<<BigInt(bits))+BigInt(r.int(3)))};
    }else if(u<.45)runs[j]={...t,count:String(n>1n?1n+(n-1n>>BigInt(1+r.int(5))):1n)};
    else if(u<.59){
      const q=randomType(r);
      if(n>1n){const k=n/2n;runs.splice(j,1,{...t,count:String(k)},{...q,count:String(n-k)});}
      else runs.splice(j+1,0,q);
    }else if(u<.67&&runs.length>2)runs.splice(j,1);
    else if(u<.77){const q=randomType(r);runs[j]={...t,[r()<.5?"p":"q"]:r()<.5?q.p:q.q};}
    else{
      const side=r()<.5?"a":"b",v=t[side].map(x=>x.slice()),i=r.int(2),k=r.int(2);
      v[i][k]=Math.max(-64,Math.min(64,v[i][k]+(r()<.5?-1:1)));runs[j]={...t,[side]:v};
    }
    return {...g,runs};
  }
  // Expansion is used only when the caller's computational budget allows
  // it. There is no machine-word or matrix-allocation limit on the genome.
  function expand(g,work=80000){
    const n=dimension(validate(g));if(n**3n>BigInt(work)*16n||n>BigInt(Number.MAX_SAFE_INTEGER))return null;
    const a=[],b=[],p=[],q=[],gates=[],exact=[];
    for(const t of g.runs)for(let j=0;j<Number(t.count);j++){a.push(...t.a);b.push(...t.b);p.push(t.p);q.push(t.q);}
    function gate(i,j,[x,y,d]){
      if(i>j){[i,j]=[j,i];x=-x;}
      gates.push([i,j,x/d,y/d]);exact.push([i,j,String(x),String(y),String(d)]);
    }
    const m=p.length;for(let j=0;j<m;j++)gate(2*j,2*j+1,p[j]);
    for(let j=0;j<m;j++)gate(2*j+1,2*((j+1)%m),q[j]);
    return {dense:{a,b,gates,mode:0},cert:{format:"moc-emergent-v1",a:a.map(x=>x.map(String)),b:b.map(x=>x.map(String)),gates:exact,direction:["1","0"]}};
  }
  function search(o={}){
    const r=rng(o.seed??1),steps=o.steps??1000,pop=o.population??24,pool=[],stats={evaluated:0,exactChecks:0,exactUnresolved:0,compressedChecks:0,compressedDirectionRejected:0,compressedInconclusive:0,largeUnresolved:0,maxDimension:"0",bestOptimisticGap:null};
    function put(x){
      if(pool.length<pop){pool.push(x);return;}
      // Keep a large-structure frontier as well as fit local proposals.
      if(r()<.18){pool[r.int(pool.length)]=x;return;}
      let w=0;for(let i=1;i<pool.length;i++)if(pool[i].e.score<pool[w].e.score)w=i;
      if(x.e.score>pool[w].e.score)pool[w]=x;
    }
    for(const x of (o.frontier||[]).slice(0,pop))if(x.g&&x.g.runs.length**3<=(o.work??80000)*16)put({g:x.g,e:evaluate(x.g,o)});
    for(let k=0;k<steps;k++){
      const g=pool.length&&r()<.90?mutate(pool[r.int(pool.length)].g,r):restart(r);
      if(g.runs.length**3>(o.work??80000)*16)continue;
      const e=evaluate(g,o);stats.evaluated++;const n=BigInt(e.dimension);
      if(n>BigInt(stats.maxDimension))stats.maxDimension=e.dimension;
      if(e.gap!==null&&(stats.bestOptimisticGap===null||e.gap>stats.bestOptimisticGap))stats.bestOptimisticGap=e.gap;
      if(e.gap!==null&&e.gap>1e-10){
        const x=expand(g,o.work??80000);
        if(!x){
          stats.largeUnresolved++;
          if(o.compressedVerify&&k%(o.proofEvery??8)===0){
            stats.compressedChecks++;
            const r=o.compressedVerify(g,e.dir,o.proofWork??3000,o.precision??192);
            if(r.proof.status==="CERTIFIED")return {status:"CERTIFIED",certificate:r.certificate,stats};
            if(r.proof.status==="NOT_SEPARATED")stats.compressedDirectionRejected++;
            else stats.compressedInconclusive++;
          }
        }else{
          stats.exactChecks++;x.cert.direction=e.dir.map(x=>String(BigInt(Math.round(1e9*x))));
          if(x.cert.direction.every(x=>x==="0"))x.cert.direction=["1","0"];
          const proof=core.verify(x.cert,o.exactWork??1000000,true);
          if(proof.status==="CERTIFIED")return {status:"CERTIFIED",certificate:{...x.cert,direction:proof.direction,proof},stats};
          if(proof.status==="INCONCLUSIVE")stats.exactUnresolved++;
        }
      }else if(n**3n>BigInt(o.work??80000)*16n)stats.largeUnresolved++;
      put({g,e});
    }
    return {status:"NO_CERTIFIED_COUNTEREXAMPLE",stats,frontier:pool};
  }
  function selftest(){
    const r=rng(81);let count=0,err=0;
    function assert(x,msg){if(!x)throw Error("cyclic selftest: "+msg);count++;}
    for(let i=0;i<50;i++){
      const g=restart(r);g.runs[0].count=String(1+r.int(4));g.runs[1].count=String(1+r.int(4));
      if(i%3===0)g.runs.push(randomType(r));
      const x=expand(g,1000000),D=core.determinant(core.sumMatrix(x.dense.a,x.dense.b,core.mixer(x.dense))),d=relative(determinant(g),0n);
      const delta=abs(sub(D,d))/Math.max(1,abs(D),abs(d));err=Math.max(err,delta);assert(delta<1e-7,"transfer determinant versus dense normal sum");
    }
    const g=restart(r);g.runs[0].count="499999999";
    const data=new Map();let hits=0,miss=0;const cache={get(k){if(data.has(k)){hits++;return data.get(k);}miss++;},set(k,v){data.set(k,v);}};
    const huge=evaluate(g,{cache,cycleSamples:8});assert(huge.dimension==="1000000000","billion-dimensional exact count");assert(huge.determinant.slice(0,2).every(Number.isFinite),"scaled determinant");assert(expand(g)===null,"no large allocation");
    const before=hits;g.runs[0].count="999999999";const grown=evaluate(g,{cache,cycleSamples:8});assert(hits>before,"transfer powers reused on growth");assert(grown.dimension==="2000000000","growth");
    g.runs[0].count="1000000000000000000000000000000";const vast=evaluate(g,{cache,cycleSamples:4});assert(BigInt(vast.dimension)>BigInt(Number.MAX_SAFE_INTEGER),"beyond machine integer dimension");assert(vast.status==="UNRESOLVED_NUMERICAL","no false certification");
    const a=search({seed:41,steps:80,work:2000,exactWork:3000,cycleSamples:5,cache,population:12});
    return {status:"PASS",assertions:count,maxRelativeDetError:err,billion:huge,larger:grown.dimension,beyondMachineInteger:vast.dimension,cacheHits:hits,cacheMisses:miss,smoke:a.stats};
  }
  return {dimension,determinant,evaluate,expand,search,selftest,validate};
}
module.exports=buildCyclic(require("./emergent.js"));
