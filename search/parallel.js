"use strict";
// Persistent shared-cache parallel coordinator. Node.js 18+.
function createDiskCache(fs,path,crypto,dir,opts={}){
  const hash=x=>crypto.createHash("sha256").update(x).digest("hex"),data=path.join(dir,"objects-v1"),memory=new Map(),pending=new Map();
  const maxMemory=(opts.memoryMb??32)*1048576,maxDisk=(opts.cacheMaxMb??4096)*1048576;
  let memoryBytes=0,diskBytes=0,flushCount=0;
  const stats={memoryHits:0,diskHits:0,misses:0,writes:0,skipped:0,corrupt:0,writeErrors:0,bytesWritten:0};
  fs.mkdirSync(data,{recursive:true});
  function scan(){
    let n=0;
    try{for(const d of fs.readdirSync(data,{withFileTypes:true}))if(d.isDirectory())for(const e of fs.readdirSync(path.join(data,d.name),{withFileTypes:true}))if(e.isFile()&&e.name.endsWith(".json"))try{n+=fs.statSync(path.join(data,d.name,e.name)).size;}catch(_){}}
    catch(_){}diskBytes=n;
  }
  scan();
  function location(k){const h=hash(k);return path.join(data,h.slice(0,2),h+".json");}
  function remember(k,v,persisted,payload){
    const old=memory.get(k);if(old)memoryBytes-=old.bytes;
    const entry={v,persisted,bytes:2*(k.length+(payload??JSON.stringify(v)).length)+128};memory.delete(k);memory.set(k,entry);memoryBytes+=entry.bytes;
    while(memoryBytes>maxMemory&&memory.size){const first=memory.keys().next().value;memoryBytes-=memory.get(first).bytes;memory.delete(first);}
    return entry;
  }
  function flush(){
    if(!pending.size)return;
    if(++flushCount%16===0)scan();
    for(const [k,payload] of pending){
      if(diskBytes>=maxDisk){stats.skipped++;continue;}
      const file=location(k),body=JSON.stringify({key:k,checksum:hash(payload),payload});
      if(body.length>2*1048576){stats.skipped++;continue;}
      let tmp=null;
      try{
        if(fs.existsSync(file)){const e=memory.get(k);if(e)e.persisted=true;continue;}
        fs.mkdirSync(path.dirname(file),{recursive:true});
        tmp=file+"."+process.pid+"."+crypto.randomBytes(6).toString("hex")+".tmp";
        fs.writeFileSync(tmp,body,{flag:"wx"});
        // Atomic publication; a reader never sees a partial JSON object.
        // Concurrent identical keys are harmless, even on a shared filesystem.
        fs.renameSync(tmp,file);tmp=null;const bytes=Buffer.byteLength(body);
        diskBytes+=bytes;stats.writes++;stats.bytesWritten+=bytes;
        const e=memory.get(k);if(e)e.persisted=true;
      }catch(_){stats.writeErrors++;}finally{if(tmp)try{fs.unlinkSync(tmp);}catch(_){}}
    }
    pending.clear();
  }
  function queue(k,v,payload){if(!pending.has(k))pending.set(k,payload??JSON.stringify(v));if(pending.size>=64)flush();}
  return {
    get(k){
      const e=memory.get(k);
      if(e){stats.memoryHits++;memory.delete(k);memory.set(k,e);if(!e.persisted)queue(k,e.v);return e.v;}
      try{
        const f=location(k),body=JSON.parse(fs.readFileSync(f,"utf8"));
        if(body.key!==k||hash(body.payload)!==body.checksum)throw Error("cache checksum mismatch");
        const v=JSON.parse(body.payload);stats.diskHits++;remember(k,v,true,body.payload);return v;
      }catch(e){if(e.code!=="ENOENT"){stats.corrupt++;try{fs.unlinkSync(location(k));}catch(_){}}stats.misses++;return undefined;}
    },
    set(k,v){
      const payload=JSON.stringify(v);remember(k,v,false,payload);
      // Persist large/expensive hulls, complete results, and matrix powers.
      // Tiny states and scalar powers are promoted on their second access.
      if(!k.startsWith("hull-v3:")&&!k.startsWith("cycle-power-v1:scalar:")||
        k.startsWith("hull-v3:")&&(v.length>=8||k.length>=480))queue(k,v,payload);
    },
    flush,stats:()=>({...stats,memoryBytes,diskBytes,pending:pending.size})
  };
}
function buildScheduler(core,cyclic,fs,path,crypto,threads,os){
  const {Worker,isMainThread,parentPort,workerData}=threads;
  const hash=x=>crypto.createHash("sha256").update(x).digest("hex");
  const print=x=>process.stdout.write(JSON.stringify(x)+"\n");
  const defaults={steps:100000,batch:250,workers:Math.max(1,Math.min(8,os.availableParallelism?os.availableParallelism():os.cpus().length)),seed:2026,population:24,archive:128,work:80000,exactWork:1000000,samples:40,cycleSamples:12,cycleShare:.4,cacheDir:".moc-cache",runId:"default",memoryMb:32,cacheMaxMb:4096,out:"moc-counterexample.json"};
  function parse(v){
    const o={...defaults};for(let i=0;i<v.length;i+=2){
      if(!v[i].startsWith("--")||i+1>=v.length)throw Error("expected --option value");
      const k=v[i].slice(2).replace(/-([a-z])/g,(_,c)=>c.toUpperCase());if(!(k in defaults)||!Object.hasOwn(defaults,k))throw Error("unknown option "+v[i]);
      if(typeof defaults[k]==="string")o[k]=v[i+1];
      else{
        const n=Number(v[i+1]);if(k==="cycleShare"){if(!Number.isFinite(n)||n<0||n>1)throw Error("cycle share must be in [0,1]");}
        else if(!Number.isSafeInteger(n)||n<(k==="seed"?0:1))throw Error("invalid "+k);o[k]=n;
      }
    }
    if(!/^[a-zA-Z0-9_-]+$/.test(o.runId))throw Error("invalid run id");return o;
  }
  function atomic(file,value){
    const tmp=file+"."+process.pid+"."+crypto.randomBytes(6).toString("hex")+".tmp";
    fs.mkdirSync(path.dirname(file),{recursive:true});
    let fd;try{fd=fs.openSync(tmp,"wx");fs.writeFileSync(fd,JSON.stringify(value,null,2)+"\n");fs.fsyncSync(fd);fs.closeSync(fd);fd=undefined;fs.renameSync(tmp,file);}
    finally{if(fd!==undefined)fs.closeSync(fd);try{fs.unlinkSync(tmp);}catch(_){}}
  }
  function read(file){try{return JSON.parse(fs.readFileSync(file,"utf8"));}catch(e){if(e.code==="ENOENT")return null;throw e;}}
  function seedFor(seed,id){return parseInt(hash(seed+":"+id).slice(0,8),16)>>>0;}
  function fresh(o){
    return {version:"moc-parallel-v1",seed:o.seed,issued:0,completed:0,nextId:0,pending:[],frontiers:{dense:[],cycle:[]},stats:{dense:{evaluated:0,complete:0,dimensions:{},bestGap:null},cycle:{evaluated:0,exactChecks:0,exactUnresolved:0,largeUnresolved:0,maxDimension:"0",bestOptimisticGap:null},cache:{memoryHits:0,diskHits:0,misses:0,writes:0,skipped:0,corrupt:0,writeErrors:0,bytesWritten:0}},certified:null};
  }
  function mergeFrontier(state,lane,incoming,o){
    const uniq=new Map();
    for(const x of state.frontiers[lane].concat(incoming||[])){
      const key=hash(JSON.stringify(x.g)),score=lane==="dense"?x.score:x.e.score,prev=uniq.get(key);
      if(!prev||score>(lane==="dense"?prev.score:prev.e.score))uniq.set(key,x);
    }
    const xs=[...uniq.values()],score=x=>lane==="dense"?x.score:x.e.score;
    xs.sort((a,b)=>score(b)-score(a));
    const elite=xs.slice(0,Math.ceil(o.archive*.6)),chosen=new Set(elite),rest=xs.filter(x=>!chosen.has(x));
    // Reserve space for structural diversity and large lineages without
    // creating order buckets or assigning a dimension to a worker.
    if(lane==="cycle")rest.sort((a,b)=>{const x=BigInt(a.e.dimension),y=BigInt(b.e.dimension);return x>y?-1:x<y?1:0;});
    else rest.sort((a,b)=>b.descriptor[0]-a.descriptor[0]);
    const diverse=rest.slice(0,Math.ceil(o.archive*.2));for(const x of diverse)chosen.add(x);
    const tail=rest.filter(x=>!chosen.has(x)).sort((a,b)=>hash(JSON.stringify(a.g)).localeCompare(hash(JSON.stringify(b.g))));
    state.frontiers[lane]=elite.concat(diverse,tail).slice(0,o.archive);
  }
  function migrants(state,lane,o,id){
    const a=state.frontiers[lane],n=Math.min(a.length,o.population),out=[],seen=new Set();
    for(let i=0;i<Math.ceil(n/3);i++){out.push(a[i]);seen.add(i);}
    for(let k=0;out.length<n&&k<a.length*4;k++){const j=seedFor(o.seed,id+":"+k)%a.length;if(!seen.has(j)){seen.add(j);out.push(a[j]);}}
    return out;
  }
  function addStats(state,job,r,delta){
    const s=state.stats[job.lane],x=r.stats||{};
    for(const k of ["evaluated","complete","exactChecks","exactUnresolved","largeUnresolved"])if(k in s)s[k]+=x[k]||0;
    if(job.lane==="dense"){
      for(const [n,c] of Object.entries(x.dimensions||{}))s.dimensions[n]=(s.dimensions[n]||0)+c;
      if(x.best?.gap!=null&&(s.bestGap===null||x.best.gap>s.bestGap))s.bestGap=x.best.gap;
    }else{
      if(BigInt(x.maxDimension||"0")>BigInt(s.maxDimension))s.maxDimension=x.maxDimension;
      if(x.bestOptimisticGap!=null&&(s.bestOptimisticGap===null||x.bestOptimisticGap>s.bestOptimisticGap))s.bestOptimisticGap=x.bestOptimisticGap;
    }
    for(const k of Object.keys(state.stats.cache))state.stats.cache[k]+=delta[k]||0;
  }
  function runJob(job,o,cache){
    const before=cache.stats(),opts={...o,steps:job.count,seed:job.seed,frontier:job.frontier,cache,returnFrontier:true,reportEvery:0};
    const r=job.lane==="dense"?core.search(opts):cyclic.search(opts);cache.flush();
    const after=cache.stats(),delta={};for(const k of Object.keys(after))delta[k]=after[k]-(before[k]||0);
    return {id:job.id,result:r,cache:delta};
  }
  function coordinator(o,filename){
    const dir=path.resolve(o.cacheDir),folder=path.join(dir,"runs",o.runId),file=path.join(folder,"checkpoint.json"),lock=path.join(folder,"coordinator.lock");
    fs.mkdirSync(folder,{recursive:true});
    // One coordinator per run ID; other run IDs may share the same cache.
    try{fs.writeFileSync(lock,JSON.stringify({pid:process.pid,host:os.hostname()}),{flag:"wx"});}
    catch(e){if(e.code==="EEXIST")throw Error("run locked: "+lock+" (remove only after confirming the previous coordinator stopped)");throw e;}
    let locked=true;const release=()=>{if(locked){locked=false;try{fs.unlinkSync(lock);}catch(_){}}};
    process.once("exit",release);
    let state;
    try{
      state=read(file)||fresh(o);if(state.version!=="moc-parallel-v1"||state.seed!==o.seed)throw Error("checkpoint version/seed mismatch; choose another run id");
      if(state.issued>o.steps)throw Error("steps is a cumulative target; choose >= "+state.issued);
    }catch(e){release();throw e;}
    const save=()=>atomic(file,state),ws=[],active=new Map(),retry=state.pending.slice(),retries=new Map();
    let stopping=false,done=false;
    function finish(status,extra={}){
      if(done)return;done=true;stopping=true;save();for(const w of ws)w.terminate();release();
      print({status,checkpoint:file,completed:state.completed,issued:state.issued,pending:state.pending.length,stats:state.stats,...extra});
    }
    if(state.certified){
      const proof=core.verify(state.certified, o.exactWork);
      if(proof.status!=="CERTIFIED"){release();throw Error("saved certificate could not be reverified at this budget");}
      atomic(path.resolve(o.out),{...state.certified,proof});finish("CERTIFIED",{certificate:path.resolve(o.out)});return;
    }
    function next(){
      if(retry.length)return retry.shift();
      if(state.issued>=o.steps)return null;
      const id=state.nextId++,count=Math.min(o.batch,o.steps-state.issued),seed=seedFor(o.seed,id);
      const lane=(seedFor(o.seed,"lane:"+id)/4294967296)<o.cycleShare?"cycle":"dense";
      const job={id,count,seed,lane,frontier:migrants(state,lane,o,id)};
      state.pending.push(job);state.issued+=count;save();return job;
    }
    function dispatch(w){
      if(stopping||done)return;
      const job=next();if(!job){if(!active.size)finish("NO_CERTIFIED_COUNTEREXAMPLE");return;}
      active.set(w,job);w.postMessage(job);
    }
    function receive(w,msg){
      if(done)return;const job=active.get(w);if(!job||job.id!==msg.id){finish("ERROR",{error:"worker job mismatch"});process.exitCode=2;return;}
      active.delete(w);const r=msg.result;
      if(r.status==="CERTIFIED"){
        // Never trust a cached score or a worker's stored proof summary.
        const proof=core.verify(r.certificate,o.exactWork);
        if(proof.status!=="CERTIFIED"){finish("ERROR",{error:"independent certificate recheck failed"});process.exitCode=2;return;}
        state.certified={...r.certificate,proof};
      }
      state.pending=state.pending.filter(x=>x.id!==job.id);state.completed+=job.count;
      addStats(state,job,r,msg.cache);mergeFrontier(state,job.lane,r.frontier,o);save();
      print({batch:job.id,lane:job.lane,completed:state.completed,target:o.steps,stats:state.stats,archive:{dense:state.frontiers.dense.length,cycle:state.frontiers.cycle.length}});
      if(state.certified){atomic(path.resolve(o.out),state.certified);finish("CERTIFIED",{certificate:path.resolve(o.out)});return;}
      if(stopping){if(!active.size)finish("CHECKPOINTED");return;}
      dispatch(w);
    }
    function failed(w,e){
      if(done||!ws.includes(w))return;const job=active.get(w);active.delete(w);
      const i=ws.indexOf(w);ws.splice(i,1);w.terminate();
      if(job){const n=(retries.get(job.id)||0)+1;retries.set(job.id,n);if(n>2){finish("ERROR",{error:String(e),failedJob:job.id});process.exitCode=2;return;}retry.unshift(job);}
      if(stopping){if(!active.size)finish("CHECKPOINTED");return;}
      spawn();
    }
    function spawn(){
      if(done||stopping)return;
      const w=new Worker(filename,{workerData:{mocParallel:true,o:{...o,cacheDir:dir}}});ws.push(w);
      w.on("message",m=>receive(w,m));w.on("error",e=>failed(w,e));w.on("exit",code=>{if(!done)failed(w,Error("worker exit "+code));});dispatch(w);
    }
    process.once("SIGINT",()=>{stopping=true;save();if(!active.size)finish("CHECKPOINTED");});
    process.once("SIGTERM",()=>{stopping=true;save();if(!active.size)finish("CHECKPOINTED");});
    print({status:"START",checkpoint:file,workers:o.workers,completed:state.completed,issued:state.issued,target:o.steps,resuming:state.completed>0||state.pending.length>0});
    if(state.completed>=o.steps&&!state.pending.length){finish("NO_CERTIFIED_COUNTEREXAMPLE");return;}
    for(let i=0;i<o.workers&&!done;i++)spawn();
  }
  function main(argv,filename,createCache){
    if(!isMainThread&&workerData?.mocParallel){
      const o=workerData.o,cache=createCache(fs,path,crypto,o.cacheDir,o);
      parentPort.on("message",job=>{parentPort.postMessage(runJob(job,o,cache));});return;
    }
    const [cmd="search",...rest]=argv;
    if(cmd==="selftest"){print({dense:core.selftest(),cycle:cyclic.selftest()});return;}
    if(cmd==="search"){coordinator(parse(rest),filename);return;}
    if(cmd==="inspect"){
      if(rest.length!==1)throw Error("inspect requires checkpoint or cyclic-genome JSON file");
      const g=read(rest[0]);if(g?.format==="moc-cycle-rle-v1")print(cyclic.evaluate(g));else if(g?.version==="moc-parallel-v1")print({completed:g.completed,pending:g.pending.length,stats:g.stats});else throw Error("unknown file format");return;
    }
    throw Error("commands: search, selftest, inspect");
  }
  return {main,parse,runJob,fresh,mergeFrontier,migrants,addStats};
}
if(require.main===module){
  try{
    const scheduler=buildScheduler(require("./emergent.js"),require("./cyclic.js"),require("node:fs"),require("node:path"),require("node:crypto"),require("node:worker_threads"),require("node:os"));
    scheduler.main(process.argv.slice(2),__filename,createDiskCache);
  }catch(e){console.error(e.stack||String(e));process.exitCode=2;}
}
module.exports={createDiskCache,buildScheduler};
