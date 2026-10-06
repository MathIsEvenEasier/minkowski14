export const TAU=2*Math.PI;
export const root=j=>[Math.cos(TAU*j/14),Math.sin(TAU*j/14)];
export const rho=2*Math.cos(TAU/7);
export const parameterValue=([a,b,c])=>a+b*rho+c*rho*rho;
export function sidePoint(j,t){const a=root(j),b=root(j+1);return a.map((x,i)=>(1-t)*x+t*b[i]);}
export function coordinateValue(a){return a.reduce((p,v,j)=>[p[0]+v*root(j)[0],p[1]+v*root(j)[1]],[0,0]);}
export function polygonNorm(p){return Math.max(...Array.from({length:14},(_,j)=>{const angle=TAU*(j+.5)/14;return (p[0]*Math.cos(angle)+p[1]*Math.sin(angle))/Math.cos(Math.PI/14);}));}
export const clamp=(x,a,b)=>Math.max(a,Math.min(b,x));
export function witnessAt(data,index){const [u,v,k]=data.witnesses[index];const parameter=data.parameters[Math.floor(k/14)];return {u,v,k,side:k%14,parameter,t:parameterValue(parameter)};}
