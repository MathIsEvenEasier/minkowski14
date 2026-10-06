import test from 'node:test';
import assert from 'node:assert/strict';
import {readFileSync} from 'node:fs';
import {sidePoint,polygonNorm,coordinateValue,witnessAt,root} from '../docs/math.mjs';
const close=(a,b)=>assert.ok(Math.abs(a-b)<1e-11,`${a} differs from ${b}`);
test('support formula gives norm one along every polygon side',()=>{for(let j=0;j<14;j++)for(const t of [0,.37,1])close(polygonNorm(sidePoint(j,t)),1);});
test('scaling and the Euclidean distinction shown in the UI',()=>{for(const r of [0,.45,1,1.5]){const p=sidePoint(0,.5).map(x=>r*x);close(polygonNorm(p),r);close(Math.hypot(...p),r*Math.cos(Math.PI/14));}});
test('integer coordinates display the certified witnesses, including chunk boundaries',()=>{const g=JSON.parse(readFileSync(new URL('../docs/graph.json',import.meta.url)));for(const n of [0,499,500,7000,13754]){const w=witnessAt(g,n),a=coordinateValue(g.coordinates[w.u]),b=coordinateValue(g.coordinates[w.v]),p=sidePoint(w.side,w.t);for(let k=0;k<2;k++)close(a[k]-b[k],p[k]);close(polygonNorm(a.map((v,k)=>v-b[k])),1);assert.ok(w.t>=-1e-12&&w.t<=1+1e-12);}});
test('rotation conventions and coordinate basis agree',()=>{for(let k=0;k<6;k++){const a=Array(6).fill(0);a[k]=1;coordinateValue(a).forEach((v,i)=>close(v,root(k)[i]));}});
