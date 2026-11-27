"use strict";
// Rigorous compressed directional verification with bounded dyadic balls.
function buildCycleProof(cyclic){
  "use strict";
  class Budget extends Error{}
  const max=(a,b)=>a>b?a:b,min=(a,b)=>a<b?a:b,abs=x=>x<0n?-x:x;
  const bits=x=>abs(x).toString(2).length;
  // A complex ball [r,i,error,exp] encloses z with
  // |Re(z/2^exp)-r|+|Im(z/2^exp)-i| <= error.
  // Every rounding operation enlarges the radius outwards.
  function arithmetic(precision){
    const P=BigInt(precision),Z=[0n,0n,0n,0n];
    function down(x,k){
      if(k===0n)return x;
      if(k>BigInt(Math.max(bits(x[0]),bits(x[1]),bits(x[2]))+2))return [0n,0n,(x[0]||x[1]||x[2])?1n:0n,x[3]+k];
      const d=1n<<k,r=x[0]/d,i=x[1]/d,e=x[2]+abs(x[0]-r*d)+abs(x[1]-i*d);
      return [r,i,(e+d-1n)/d,x[3]+k];
    }
    function norm(x){
      const m=abs(x[0])+abs(x[1])+x[2];if(!m)return Z;
      const k=BigInt(bits(m))-P;
      if(k>0n)return down(x,k);
      if(k<0n){const d=1n<<(-k);return [x[0]*d,x[1]*d,x[2]*d,x[3]+k];}
      return x;
    }
    const integer=(x,y=0n)=>norm([x,y,0n,0n]),O=integer(1n);
    function rational(x,y,d){
      if(d<=0n)throw Error("nonpositive rational denominator");
      const s=1n<<P,r=x*s/d,i=y*s/d;
      return norm([r,i,BigInt((x*s%d!==0n?1:0)+(y*s%d!==0n?1:0)),-P]);
    }
    function add(a,b){
      if(a[0]===0n&&a[1]===0n&&a[2]===0n)return b;
      if(b[0]===0n&&b[1]===0n&&b[2]===0n)return a;
      const e=max(a[3],b[3]),x=down(a,e-a[3]),y=down(b,e-b[3]);
      return norm([x[0]+y[0],x[1]+y[1],x[2]+y[2],e]);
    }
    const neg=a=>[-a[0],-a[1],a[2],a[3]];
    function mul(a,b){
      return norm([a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0],
        (abs(a[0])+abs(a[1]))*b[2]+(abs(b[0])+abs(b[1]))*a[2]+a[2]*b[2],a[3]+b[3]]);
    }
    function compare(a,e,b,f){
      if(a===b&&e===f)return 0;if(a===0n)return b>0n?-1:b<0n?1:0;if(b===0n)return a>0n?1:-1;
      if(a<0n&&b>=0n)return -1;if(a>=0n&&b<0n)return 1;
      if(a<0n)return -compare(-a,e,-b,f);
      const l=BigInt(bits(a))+e,r=BigInt(bits(b))+f;if(l!==r)return l<r?-1:1;
      if(e<f)b<<=f-e;else a<<=e-f;
      return a<b?-1:a>b?1:0;
    }
    const project=(a,e)=>{const c=a[0]*e[0]+a[1]*e[1],r=max(abs(e[0]),abs(e[1]))*a[2];return [c-r,c+r,a[3]];};
    const powerCache=new Map();
    function pow(base,n,identity,op,kind){
      let out=identity,x=base,bit=0;const key=kind+":"+base.flat().map(String).join(",")+":";
      while(n>0n){
        if(bit>0){const k=key+bit,old=powerCache.get(k);if(old)x=old;else{x=op(x,x);if(powerCache.size<50000)powerCache.set(k,x);}}
        if(n&1n)out=op(x,out);n>>=1n;bit++;
      }return out;
    }
    const I=[O,Z,Z,O],mm=(a,b)=>[add(mul(a[0],b[0]),mul(a[1],b[2])),add(mul(a[0],b[1]),mul(a[1],b[3])),add(mul(a[2],b[0]),mul(a[3],b[2])),add(mul(a[2],b[1]),mul(a[3],b[3]))];
    return {Z,O,I,integer,rational,add,neg,mul,compare,project,mm,conj:a=>[a[0],-a[1],a[2],a[3]],cp:(a,n)=>pow(a,n,O,mul,"c"),mp:(a,n)=>pow(a,n,I,mm,"m")};
  }
  const vadd=(a,b)=>[a[0]+b[0],a[1]+b[1]],vsub=(a,b)=>[a[0]-b[0],a[1]-b[1]],vmul=(a,b)=>[a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]],vs=(a,s)=>[a[0]*s,a[1]*s];
  function determinant(g,A){
    if(g.extra)return cyclic.oddDeterminant(g,A);
    const {Z,O,I,rational,add,neg,mul,mm,mp,cp}=A;
    function block(x,y,gate,inverse=false){
      x=x.map(BigInt);y=y.map(BigInt);let [s,t,q]=gate.map(BigInt);
      const d=q*q+s*s+t*t,c=q*q-s*s-t*t;let sr=2n*q*s,si=2n*q*t;if(inverse){sr=-sr;si=-si;}
      const w=sr*sr+si*si,den=d*d,dx=vsub(x,y),r=a=>rational(a[0],a[1],den);
      return {l:r(vadd(vs(x,c*c),vs(y,w))),r:r(vadd(vs(x,w),vs(y,c*c))),u:r(vs(vmul([sr,-si],dx),c)),v:r(vs(vmul([sr,si],dx),c))};
    }
    function cell(p,t,q){
      const B=block(t.b[0],t.b[1],t.p),L=block(p.a[1],t.a[0],p.q,true),R=block(t.a[1],q.a[0],t.q,true),transfer=(d,w)=>[d,neg(w),O,Z];
      return {T:mm(transfer(add(B.r,R.l),mul(B.u,B.v)),transfer(add(B.l,L.r),mul(L.u,L.v))),u:mul(B.u,R.u),v:mul(B.v,R.v)};
    }
    let T=I,u=O,v=O;const a=g.runs,r=a.length;
    function append(x,n){if(!n)return;T=mm(mp(x.T,n),T);u=mul(cp(x.u,n),u);v=mul(cp(x.v,n),v);}
    for(let j=0;j<r;j++){
      const t=a[j],p=a[(j+r-1)%r],q=a[(j+1)%r],n=BigInt(t.count);
      if(n===1n)append(cell(p,t,q),1n);
      else{append(cell(p,t,t),1n);if(n>2n)append(cell(t,t,t),n-2n);append(cell(t,t,q),1n);}
    }
    return add(add(T[0],T[3]),neg(add(u,v)));
  }
  function types(g,side){
    const m=new Map();for(const t of g.runs)for(const z of t[side]){const k=JSON.stringify(z),v=m.get(k)||{z:z.map(BigInt),count:0n};v.count+=BigInt(t.count);m.set(k,v);}
    if(g.extra){const z=g.extra[side],k=JSON.stringify(z),v=m.get(k)||{z:z.map(BigInt),count:0n};v.count++;m.set(k,v);}
    return [...m.values()];
  }
  function verify(cert,work=10000){
    if(cert.format!=="moc-cycle-interval-v1")throw Error("unknown compressed certificate");
    const g=cyclic.validate(cert.genome),n=cyclic.dimension(g),precision=cert.precision;
    if(!Number.isSafeInteger(precision)||precision<64||precision>65536||!Number.isSafeInteger(work)||work<1)throw Error("invalid interval precision or work limit");
    if(!Array.isArray(cert.direction)||cert.direction.length!==2||cert.direction.some(x=>typeof x!=="string"||!/^[-]?\d+$/.test(x)))throw Error("invalid direction");
    const e=cert.direction.map(BigInt);if(!e[0]&&!e[1])throw Error("zero direction");
    const A=arithmetic(precision),{O,integer,mul,cp,project,compare}=A;
    let visited=0,pruned=0,leaves=0,ambiguous=0,matchingFound=false;
    const tick=()=>{if(++visited>work)throw new Budget();};
    const D=determinant(g,A),d=project(D,e),D2=d[0]>0n?[d[0]*d[0],2n*d[2]]:null;
    const a=types(g,"a"),b=types(g,"b"),m=a.length,k=b.length,cap=b.map(x=>x.count);
    const z=a.map(x=>b.map(y=>vadd(x.z,y.z))),sq=z.map(row=>row.map(v=>v[0]*v[0]+v[1]*v[1]));
    const Z=z.map(row=>row.map(v=>integer(v[0],v[1]))),S=sq.map(row=>row.map(v=>integer(v)));
    const rowMax=sq.map(row=>row.reduce(max,0n)),tails=Array(m+1);tails[m]=O;
    for(let i=m-1;i>=0;i--)tails[i]=mul(cp(integer(rowMax[i]),a[i].count),tails[i+1]);
    const e2=integer(e[0]*e[0]+e[1]*e[1]);
    function leaf(p){
      leaves++;const h=project(p,e);
      if(compare(h[1],h[2],d[0],d[2])<0)return true;
      if(compare(h[0],h[2],d[1],d[2])>=0){matchingFound=true;return false;}
      ambiguous++;return null;
    }
    function bound(p,i,j,R,lo){
      if(!D2)return false;
      const maxsq=sq[i].slice(j).reduce(max,0n);
      const q=mul(mul(mul(p,cp(S[i][j],lo)),cp(integer(maxsq),R-lo)),tails[i+1]),u=mul(e2,q);
      return compare(u[0]+u[2],u[3],D2[0],D2[1])<0;
    }
    // A grouped assignment is a nonnegative integer transportation table.
    // Every labelled permutation gives one table, and every table with
    // these marginals lifts to a labelled permutation. No labelled
    // permutation or dimension-sized array is enumerated here.
    function visit(i,j,R,p,p2){
      tick();if(i===m)return leaf(p);
      if(j===k){if(R!==0n)return true;return visit(i+1,0,i+1<m?a[i+1].count:0n,p,p2);}
      let later=0n;for(let l=j+1;l<k;l++)later+=cap[l];
      const lo=max(0n,R-later),hi=min(R,cap[j]);if(lo>hi)return true;
      function range(l,h){
        tick();if(bound(p2,i,j,R,l)){pruned++;return true;}
        if(l===h){
          cap[j]-=l;
          const result=visit(i,j+1,R-l,mul(p,cp(Z[i][j],l)),mul(p2,cp(S[i][j],l)));
          cap[j]+=l;return result;
        }
        const mid=(l+h)>>1n;
        // Explore high-count intervals first; a single obstructing
        // matching product disproves the proposed strict direction.
        const first=range(mid+1n,h);if(first===false)return false;
        const second=range(l,mid);if(second===false)return false;
        return first===true&&second===true?true:null;
      }
      return range(lo,hi);
    }
    let status="INCONCLUSIVE",reason="interval-overlap";
    try{
      const result=visit(0,0,a[0].count,O,O);
      if(result===true){status="CERTIFIED";reason="all-transport-tables-strict";}
      else if(result===false){status="NOT_SEPARATED";reason="matching-product-obstructs-direction";}
    }catch(err){if(!(err instanceof Budget)&&!(err instanceof RangeError))throw err;reason=err instanceof Budget?"work-budget":"stack-resource";}
    return {status,reason,method:"rigorous-dyadic-balls-transportation",dimension:String(n),precision,visited,pruned,leaves,ambiguous,matchingFound,determinantBall:D.map(String),direction:cert.direction};
  }
  function propose(g,dir,work=5000,precision=192){
    const direction=dir.map(x=>String(BigInt(Math.round(x*1e9))));if(direction.every(x=>x==="0"))direction[0]="1";
    const cert={format:"moc-cycle-interval-v1",genome:g,direction,precision},proof=verify(cert,work);
    return {proof,certificate:{...cert,proof}};
  }
  function selftest(core){
    const A=arithmetic(96),assert=(x,m)=>{if(!x)throw Error("interval test: "+m);};
    let count=0;const ok=(x,m)=>{assert(x,m);count++;};
    function inside(ball,r,i,d=1n){
      // Compare scaled dyadic center and radius against exact rational.
      const [x,y,u,e]=ball,s=e<0n?1n<<(-e):1n,t=e>=0n?1n<<e:1n;
      return abs(r*s-x*t*d)+abs(i*s-y*t*d)<=u*t*d;
    }
    const x=A.rational(1n,2n,3n),y=A.rational(-4n,5n,7n);
    ok(inside(x,1n,2n,3n),"rational enclosure");ok(inside(A.add(x,y),-5n,29n,21n),"addition enclosure");ok(inside(A.mul(x,y),-14n,-3n,21n),"multiplication enclosure");
    const g={format:"moc-cycle-rle-v1",runs:[{count:"1",a:[[1,2],[3,1]],b:[[2,-1],[1,3]],p:[1,2,3],q:[2,1,3]},{count:"1",a:[[3,-1],[-2,1]],b:[[1,-1],[2,3]],p:[2,1,4],q:[1,3,4]}]};
    for(let j=0;j<12;j++){
      g.runs[0].a[0]=[j-4,j%3];g.runs[1].count=String(1+j%3);
      if(j%2)g.extra={a:[2,-1],b:[3,2],gate:[1,2,4]};else delete g.extra;
      const x=cyclic.expand(g,1000000),raw=core.verify(x.cert,1000000),d=raw.determinantNumerator.map(BigInt),den=BigInt(raw.denominator);
      ok(inside(determinant(g,A),d[0],d[1],den),"interval determinant contains exact rational determinant");
      const r=verify({format:"moc-cycle-interval-v1",genome:g,direction:["1","0"],precision:96},100000);
      if(raw.status==="NOT_SEPARATED")ok(r.status!=="CERTIFIED","no false certificate");else ok(r.status!=="NOT_SEPARATED","no false rejection");
    }
    delete g.extra;g.runs[0].count="499999999";g.runs[1].count="1";
    const r=verify({format:"moc-cycle-interval-v1",genome:g,direction:["1","0"],precision:192},400);
    ok(r.dimension==="1000000000","large exact dimension");ok(r.status!=="CERTIFIED","test fixture not falsely certified");
    g.extra={a:[2,-1],b:[3,2],gate:[1,2,4]};
    const odd=verify({format:"moc-cycle-interval-v1",genome:g,direction:["1","0"],precision:192},400);
    ok(odd.dimension==="1000000001","large odd exact dimension");ok(odd.status!=="CERTIFIED","odd fixture not falsely certified");
    return {status:"PASS",assertions:count,billion:r,billionPlusOne:odd};
  }
  return {verify,propose,selftest,arithmetic};
}
module.exports=buildCycleProof(require("./cyclic.js"));
