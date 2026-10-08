import {root,sidePoint,coordinateValue,clamp,witnessAt} from './math.mjs';
const $=id=>document.getElementById(id), base='https://github.com/MathIsEvenEasier/minkowski14/blob/main/formal/';
const colours=['#7653b8','#287b91','#bc4e55','#977323'];
function svgPolygon(id,j,t,r=1,mini=false){
 const el=$(id),scale=mini?148:147,cx=260,cy=198,to=p=>[cx+p[0]*scale,cy-p[1]*scale],xy=p=>to(p).map(x=>x.toFixed(2)).join(','),p=sidePoint(j,t),q=p.map(x=>r*x),a=root(j),b=root(j+1),d=[b[0]-a[0],b[1]-a[1]];
 const support=[a.map((x,i)=>x-d[i]*2.4),b.map((x,i)=>x+d[i]*2.4)];
 el.innerHTML=`<defs><marker id="${id}-arrow" viewBox="0 0 10 10" refX="8" refY="5" markerWidth="6" markerHeight="6" orient="auto"><path d="M0 0L10 5L0 10Z" fill="#d55b32"/></marker></defs>
 <path d="M50 198H470 M260 15V380" stroke="#e6e2ec" stroke-width="1"/>
 <circle cx="260" cy="198" r="147" fill="none" stroke="#dcd8e8" stroke-dasharray="3 5"/>
 <polygon points="${Array.from({length:14},(_,k)=>xy(root(k))).join(' ')}" fill="#efeafa" stroke="#8171b4" stroke-width="1.5"/>
 <line x1="${to(support[0])[0]}" y1="${to(support[0])[1]}" x2="${to(support[1])[0]}" y2="${to(support[1])[1]}" stroke="#7a798d" stroke-dasharray="5 5" stroke-width="1"/>
 <polyline points="${xy(a)} ${xy(b)}" stroke="#6651bb" stroke-width="5" fill="none"/>
 <polyline points="${cx},${cy} ${xy(q)}" stroke="#d55b32" stroke-width="2.8" fill="none" marker-end="url(#${id}-arrow)"/>
 <circle cx="${to(p)[0]}" cy="${to(p)[1]}" r="6" fill="white" stroke="#6651bb" stroke-width="2"/>
 <circle cx="${to(q)[0]}" cy="${to(q)[1]}" r="4.5" fill="#d55b32"/>
 <circle cx="260" cy="198" r="3" fill="#22213b"/><text x="249" y="219" font-family="sans-serif" font-size="13" fill="#65657a">0</text>
 ${mini?'':`<text x="${to(q)[0]+(q[0]<0?-38:11)}" y="${to(q)[1]-12}" font-family="sans-serif" font-size="14" fill="#b9512f">r·p</text><text x="24" y="380" font-family="sans-serif" font-size="12" fill="#65657a">Dashed line: a supporting line of P₁₄</text>`}`;
}
function normUI(){const j=+$('side').value,t=+$('parameter').value,r=+$('scale').value;
 $('side-out').value=String(j);$('parameter-out').value=t.toFixed(3);$('scale-out').value=r.toFixed(2);$('norm-out').textContent=r.toFixed(2);$('euclid-out').textContent=(Math.hypot(...sidePoint(j,t))*r).toFixed(3);
 $('norm-explanation').textContent=r===1?'The vector ends on a polygon side, so its polygon norm is exactly 1.':r<1?'The scaled endpoint is inside the unit ball. Homogeneity gives norm r.':'The scaled endpoint is outside the unit ball. Homogeneity gives norm r.';
 svgPolygon('unit-svg',j,t,r);
}
for(const id of ['side','parameter','scale'])$(id).addEventListener('input',normUI);
$('reset-scale').addEventListener('click',()=>{$('scale').value='1';normUI();});normUI();
const nodes={
 root:{kind:'Algebra',title:'Exact coordinates',statement:'ζ = exp(πi/7),  ζ¹⁴ = 1',text:'Define ζ as the complex number exp(πi/7). Six integer coefficients represent points; their exact arithmetic agrees with complex evaluation.',inputs:'Provides the rotations and coordinate identities used throughout the geometry.',path:'Algebra.lean'},
 norm:{kind:'Norm construction',title:'The unit ball is the fourteen-gon',statement:'‖x‖ ≤ 1  ↔  x ∈ conv{z : z¹⁴ = 1}',text:'The convex hull is compact, balanced and absorbing. Its Minkowski functional is a norm. The resulting space has real dimension two and exactly the required closed unit ball.',inputs:'Uses the geometric roots, convexity and the gauge construction. See also Plane.lean.',path:'Polygon.lean'},
 side:{kind:'Geometric lemma',title:'Every side point has norm one',statement:'‖ζʲ((1 − t) + tζ)‖ = 1  for  0 ≤ t ≤ 1',text:'Convexity puts the segment inside the unit ball, giving the upper bound. A supporting linear functional attains its maximum along that side, preventing the norm from being smaller than one. Rotation transfers this to every side.',inputs:'Uses the constructed polygon norm and root geometry. The first diagram illustrates this lemma.',path:'Facet.lean#L99'},
 edges:{kind:'Exact witnesses',title:'Every listed graph edge is a unit edge',statement:'(u,v) ∈ edges  ⇒  ‖point(u) − point(v)‖ = 1',text:'Each edge difference equals a rotated side point with parameter A + Bρ + Cρ². Lean checks the coefficient equality and the interval 0 ≤ t ≤ 1. Twenty-eight modules cover all 13,755 edges and identify them with the SAT graph’s edge list.',inputs:'Uses the side lemma, the coordinate interpretation and the 29 verified algebraic parameters.',path:'Embedding.lean'},
 encoding:{kind:'Boolean encoding',title:'A proper colouring would satisfy the clauses',statement:'proper four-colouring  ⇒  satisfying assignment',text:'Four Boolean variables encode each vertex colour. The clauses require exactly one colour per vertex and different colours across each edge. A single anchor colour removes a redundant colour permutation; any colouring can be relabelled to satisfy it.',inputs:'The formula has 6,160 variables and 65,801 clauses. The graph-to-formula correspondence is proved inside Lean.',path:'MathIsEasy/Minkowski14/GraphCertificate.lean'},
 lrat:{kind:'Refutation',title:'The clauses derive a contradiction',statement:'the colouring CNF ⊢ the empty clause',text:'The LRAT file supplies a finite sequence of logical inferences. The importer constructs proof expressions that the Lean kernel checks. Forty-two chunks lead to the empty clause: no Boolean assignment satisfies the formula.',inputs:'Uses the exact encoded formula. File reading and proof generation do not add axioms or bypass the kernel.',path:'MathIsEasy/Minkowski14LRAT/Chunk042.lean#L12'},
 finite:{kind:'Finite theorem',title:'The graph has no proper four-colouring',statement:'¬ FourColourable edges',text:'If the graph admitted a four-colouring, the encoding theorem would produce a satisfying assignment. The checked refutation excludes it. This is the finite obstruction; the geometry identifies where its vertices and edges live.',inputs:'Combines both the colouring-to-CNF bridge and the LRAT refutation.',path:'MathIsEasy/Minkowski14/GraphCertificate.lean#L20'},
 plane:{kind:'Final theorem',title:'The whole plane needs at least five colours',statement:'proper c : Plane → Fin n  ⇒  5 ≤ n',text:'Restrict a hypothetical four-colouring of the plane to the stored points. The edge theorem makes this a proper four-colouring of the finite graph, contradicting its certificate. Any colouring with fewer than four colours can also be viewed as a four-colouring.',inputs:'Uses both branches: exact unit-edge geometry and finite non-four-colourability. ',path:'Final.lean#L18'}
};
function selectNode(key,writeHash=true){const n=nodes[key];if(!n)return;
 for(const el of document.querySelectorAll('[data-node]'))el.setAttribute('aria-pressed',String(el.dataset.node===key));
 $('node-kind').textContent=n.kind;$('node-title').textContent=n.title;$('node-statement').textContent=n.statement;$('node-explanation').textContent=n.text;$('node-inputs').textContent=n.inputs;$('node-source').href=base+n.path;
 if(writeHash)history.replaceState(null,'','#proof-'+key);
}
for(const el of document.querySelectorAll('[data-node]'))el.addEventListener('click',()=>selectNode(el.dataset.node));
const requestedNode=location.hash.startsWith('#proof-')?location.hash.slice(7):'plane';
selectNode(nodes[requestedNode]?requestedNode:'plane',false);
if(location.hash.startsWith('#proof-')&&nodes[location.hash.slice(7)])$('proof-map').scrollIntoView();
let data,points,current=0,uColour=0,vColour=1;
for(const endpoint of ['u','v'])for(let c=0;c<4;c++){
 const b=document.createElement('button');b.type='button';b.className='colour-button';b.style.setProperty('--swatch',colours[c]);b.textContent=c+1;b.setAttribute('aria-label',`Colour ${c+1}`);b.dataset.colour=c;
 b.addEventListener('click',()=>{if(endpoint==='u')uColour=c;else vColour=c;colourUI();drawGraph();});$(endpoint+'-colours').append(b);
}
function colourUI(){for(const endpoint of ['u','v'])for(const b of $(endpoint+'-colours').children)b.setAttribute('aria-pressed',String(+b.dataset.colour===(endpoint==='u'?uColour:vColour)));
 const same=uColour===vColour;$('colour-result').textContent=same?`Conflict: both endpoints have colour ${uColour+1}. This edge clause is false.`:'This edge is satisfied. The full graph requires every edge to be satisfied at once.';$('colour-result').style.color=same?'var(--red)':'var(--green)';
}
function drawGraph(){if(!data)return;const canvas=$('graph-canvas'),ctx=canvas.getContext('2d'),width=900,height=650;ctx.clearRect(0,0,width,height);const {u,v}=witnessAt(data,current),zoom=+$('zoom').value;
 const extent=Math.max(...points.flat().map(Math.abs))+0.25,scale=Math.min(width,height)/(2*extent)*zoom;
 const center=zoom>1?[(points[u][0]+points[v][0])/2,(points[u][1]+points[v][1])/2]:[0,0];
 const project=p=>[width/2+(p[0]-center[0])*scale,height/2-(p[1]-center[1])*scale];
 const line=(a,b,colour,w)=>{ctx.beginPath();ctx.moveTo(...project(points[a]));ctx.lineTo(...project(points[b]));ctx.strokeStyle=colour;ctx.lineWidth=w;ctx.stroke();};
 if($('all-edges').checked)for(const [a,b] of data.witnesses)line(a,b,'#d6d1e04d',.6);
 else for(const [a,b] of data.witnesses)if(a===u||a===v||b===u||b===v)line(a,b,'#cbc4db',1.1);
 ctx.fillStyle='#81778b77';for(const p of points){ctx.beginPath();ctx.arc(...project(p),1.7,0,2*Math.PI);ctx.fill();}
 line(u,v,uColour===vColour?'#b83d47':'#d55b32',3.5);
 for(const [i,c] of [[u,uColour],[v,vColour]]){const q=project(points[i]);ctx.beginPath();ctx.arc(...q,7.5,0,2*Math.PI);ctx.fillStyle=colours[c];ctx.fill();ctx.strokeStyle='white';ctx.lineWidth=2;ctx.stroke();ctx.font='bold 16px sans-serif';ctx.fillStyle='#22213b';ctx.fillText(`v${i}`,q[0]+10,q[1]-10);}
 canvas._project=project;
}
function updateEdge(n){if(!data)return;current=clamp(Math.round(Number.isFinite(n)?n:0),0,data.witnesses.length-1);$('edge-number').value=String(current+1);const w=witnessAt(data,current);
 $('edge-title').textContent=`v${w.u} — v${w.v}`;$('u-label').textContent=`Vertex ${w.u}`;$('v-label').textContent=`Vertex ${w.v}`;
 $('edge-formula').textContent=`point(${w.u}) − point(${w.v}) = ζ^${w.side} ((1 − t) + tζ)`;
 const [a,b,c]=w.parameter;$('edge-parameter').textContent=`t = (${a}) + (${b})ρ + (${c})ρ² ≈ ${w.t.toFixed(8)}. Side j = ${w.side}.`;
 const left=data.coordinates[w.u],right=data.coordinates[w.v];$('coordinates').textContent=`v${w.u}: [${left.join(', ')}]\nv${w.v}: [${right.join(', ')}]\ndifference: [${left.map((x,i)=>x-right[i]).join(', ')}]`;
 const chunk=String(Math.floor(current/500)+1).padStart(3,'0'),line=9+current%500;$('edge-source').href=base+`Geometry/Chunk${chunk}.lean#L${line}`;
 $('graph-caption').textContent=`1,540 stored vertices. Edge ${current+1} joins v${w.u} to v${w.v}. Zoom centres on its midpoint. Click a point to inspect an incident edge.`;
 svgPolygon('edge-svg',w.side,w.t,1,true);$('prev-edge').disabled=current===0;$('next-edge').disabled=current===data.witnesses.length-1;colourUI();drawGraph();
}
$('edge-number').addEventListener('input',e=>{if(e.target.value!==''&&e.target.validity.valid)updateEdge(Number(e.target.value)-1);});
$('edge-number').addEventListener('change',e=>updateEdge(Number(e.target.value)-1));$('prev-edge').addEventListener('click',()=>updateEdge(current-1));$('next-edge').addEventListener('click',()=>updateEdge(current+1));
$('all-edges').addEventListener('change',drawGraph);$('zoom').addEventListener('input',drawGraph);
$('graph-canvas').addEventListener('click',e=>{if(!points)return;const c=e.currentTarget,b=c.getBoundingClientRect(),x=(e.clientX-b.left)*c.width/b.width,y=(e.clientY-b.top)*c.height/b.height;let best=-1,dist=20;
 points.forEach((p,i)=>{const q=c._project(p),d=Math.hypot(q[0]-x,q[1]-y);if(d<dist){best=i;dist=d;}});if(best>=0){const index=data.witnesses.findIndex(([u,v])=>u===best||v===best);if(index>=0)updateEdge(index);}});
colourUI();
try{const response=await fetch('graph.json');if(!response.ok)throw new Error('Graph unavailable');data=await response.json();points=data.coordinates.map(coordinateValue);updateEdge(0);$('load-status').textContent='';}catch(err){$('load-status').textContent='The graph could not be loaded. Reload the page or use the exact graph in the repository.';console.error(err);}
