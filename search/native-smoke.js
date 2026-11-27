"use strict";
// Run with: node search/native-smoke.js
// Exercises real worker threads, atomic files, and a resumed coordinator.
const assert=require("node:assert/strict"),fs=require("node:fs"),path=require("node:path"),os=require("node:os"),crypto=require("node:crypto"),cp=require("node:child_process");
const {createDiskCache}=require("./parallel.js");
const root=fs.mkdtempSync(path.join(os.tmpdir(),"moc-parallel-"));
try{
  const a=createDiskCache(fs,path,crypto,root,{memoryMb:1,cacheMaxMb:64});
  a.set("native-smoke-result",[1,2,3]);a.flush();
  const b=createDiskCache(fs,path,crypto,root,{memoryMb:1,cacheMaxMb:64});
  assert.deepEqual(b.get("native-smoke-result"),[1,2,3]);assert.equal(b.stats().diskHits,1);
  const key=crypto.createHash("sha256").update("native-smoke-result").digest("hex"),file=path.join(root,"objects-v1",key.slice(0,2),key+".json");
  fs.writeFileSync(file,"corrupt");
  const c=createDiskCache(fs,path,crypto,root,{memoryMb:1,cacheMaxMb:64});
  assert.equal(c.get("native-smoke-result"),undefined);assert.equal(c.stats().corrupt,1);
  const opts=["--workers","2","--batch","20","--population","8","--archive","24","--work","2000","--exact-work","4000","--proof-work","200","--cycle-samples","4","--samples","8","--cache-dir",root,"--cycle-share","0.5","--seed","41","--cache-max-mb","64"];
  function run(steps){
    const r=cp.spawnSync(process.execPath,[path.join(__dirname,"parallel.js"),"search","--steps",String(steps),...opts],{encoding:"utf8",timeout:120000,maxBuffer:8*1048576});
    if(r.error)throw r.error;assert.equal(r.status,0,r.stderr);
    const state=JSON.parse(fs.readFileSync(path.join(root,"runs","default","checkpoint.json"),"utf8"));
    assert.equal(state.completed,steps);assert.equal(state.pending.length,0);assert.equal(state.issued,steps);
    assert.equal(state.certified,null);assert.ok(state.stats.cache.writes>0);
    return state;
  }
  const first=run(60),resumed=run(100);
  assert.ok(resumed.nextId>first.nextId);assert.ok(resumed.stats.cache.memoryHits+resumed.stats.cache.diskHits>=first.stats.cache.memoryHits+first.stats.cache.diskHits);
  assert.ok(!fs.existsSync(path.join(root,"runs","default","coordinator.lock")));
  process.stdout.write(JSON.stringify({status:"PASS",first:first.completed,resumed:resumed.completed,cache:resumed.stats.cache,dense:resumed.stats.dense,cycle:resumed.stats.cycle})+"\n");
}finally{fs.rmSync(root,{recursive:true,force:true});}
