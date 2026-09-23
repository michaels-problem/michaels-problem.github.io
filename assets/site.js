function renderMath(scope=document){scope.querySelectorAll('.math:not([data-rendered])').forEach(el=>{if(window.katex){try{window.katex.render(el.textContent,el,{displayMode:el.classList.contains('display'),throwOnError:true,trust:false});el.dataset.rendered='true';}catch(err){el.classList.add('math-error');console.error('Mathematical typesetting failed:',err.message);}}});}
renderMath();
const paperViewer=document.querySelector('[data-paper-viewer]');
if(paperViewer){
 const pageSelect=paperViewer.querySelector('.paper-page-select'),pageImage=paperViewer.querySelector('.paper-page'),pageFrame=paperViewer.querySelector('.paper-page-frame');
 const previous=paperViewer.querySelector('.paper-previous'),next=paperViewer.querySelector('.paper-next'),zoom=paperViewer.querySelector('.paper-zoom');
 function showPage(value){const page=Math.max(1,Math.min(pageSelect.options.length,value));pageSelect.value=String(page);pageImage.src=`/assets/manuscript/page-${page}.png`;pageImage.alt=`Page ${page} of the original manuscript`;previous.disabled=page===1;next.disabled=page===pageSelect.options.length;paperViewer.querySelector('.paper-page-status').textContent=`Page ${page} of ${pageSelect.options.length}`;pageFrame.scrollTop=0;pageFrame.scrollLeft=0;}
 previous.addEventListener('click',()=>showPage(Number(pageSelect.value)-1));next.addEventListener('click',()=>showPage(Number(pageSelect.value)+1));pageSelect.addEventListener('change',()=>showPage(Number(pageSelect.value)));
 zoom.addEventListener('click',()=>{const enlarged=pageFrame.classList.toggle('enlarged');zoom.textContent=enlarged?'Fit width':'Enlarge page';zoom.setAttribute('aria-pressed',String(enlarged));});
 showPage(1);
}
document.addEventListener('click',async event=>{const button=event.target.closest('.copy-code');if(!button)return;const code=button.closest('.code-panel').querySelector('pre').innerText;try{await navigator.clipboard.writeText(code);button.textContent='Copied';setTimeout(()=>button.textContent='Copy',1800);}catch{button.textContent='Select and copy';}});

const htmlEscape=s=>String(s).replaceAll('&','&amp;').replaceAll('<','&lt;').replaceAll('>','&gt;').replaceAll('"','&quot;');
const termDefinitions={Character:'character',IsSubmultiplicative:'submultiplicative',IsLocallyMultiplicativelyConvex:'locally-multiplicatively-convex',BoundedOnBoundedSets:'bounded-on-bounded-sets'};
const controllerMap=new WeakMap();
let guideBook;
let returnFocus;
const dialog=document.querySelector('#definition-dialog');
function linkedTerms(text){return htmlEscape(text).replace(/\b(Character|IsSubmultiplicative|IsLocallyMultiplicativelyConvex|BoundedOnBoundedSets)\b/g,term=>`<a class="inline-term" href="/definitions/#${termDefinitions[term]}" data-definition="${termDefinitions[term]}">${term}</a>`);}
function guideCode(guide,index){
 const code=guide.id==='theorem-a'?'universe u\n\n'+guide.source:guide.source;
 const ranges=guide.steps.map((step,i)=>({index:i,start:code.indexOf(step.source),end:code.indexOf(step.source)+step.source.length,length:step.source.length}));
 const boundaries=[...new Set([0,code.length,...ranges.filter(r=>r.start>=0).flatMap(r=>[r.start,r.end])])].sort((a,b)=>a-b);
 let markup='';
 for(let i=0;i<boundaries.length-1;i++){
  const start=boundaries[i],end=boundaries[i+1],covering=ranges.filter(r=>r.start<=start&&r.end>=end&&r.start>=0).sort((a,b)=>a.length-b.length);
  const chosen=covering[0],selected=covering.some(r=>r.index===index),text=linkedTerms(code.slice(start,end));
  markup+=chosen?`<span class="clause${selected?' selected':''}" data-step="${chosen.index}" title="${htmlEscape(guide.steps[chosen.index].heading)}">${text}</span>`:text;
 }
 return markup;
}
function linkMarkup(link){
 if(link.target==='proved-theorem')return `<a href="/sources/AutomaticContinuity/TheoremA/#L34">${htmlEscape(link.label)}</a>`;
 const id=link.target.split('.')[0];
 if(id==='theorem-a')return `<a href="/#step=${encodeURIComponent(link.target)}" data-guide-link="${htmlEscape(link.target)}">${htmlEscape(link.label)}</a>`;
 return `<button type="button" data-guide-link="${htmlEscape(link.target)}">${htmlEscape(link.label)}</button>`;
}
function initialiseGuide(element,start=0){
 const guide=guideBook.guides.find(g=>g.id===element.dataset.guide);if(!guide)return;
 let current=start;
 const select=element.querySelector('.clause-select');
 function setStep(index){
  current=Math.max(0,Math.min(guide.steps.length-1,index));const step=guide.steps[current];
  element.querySelector('.guide-progress').textContent=`Clause ${current+1} of ${guide.steps.length}`;
  element.querySelector('.guide-prev').disabled=current===0;element.querySelector('.guide-next').disabled=current===guide.steps.length-1;
  select.value=String(current);element.querySelector('.guide-code').innerHTML=guideCode(guide,current);
  element.querySelector('.guide-explanation').innerHTML=`<h3>${htmlEscape(step.heading)}</h3><code class="selected-fragment">${htmlEscape(step.source)}</code><p class="guide-reading">${htmlEscape(step.reading)}</p><p>${htmlEscape(step.mathMeaning)}</p><p class="guide-role">${htmlEscape(step.role)}</p><div class="guide-links">${step.links.map(linkMarkup).join('')}<a href="${guide.sourceLink}">Full source</a></div>`;
 }
 element.querySelector('.guide-prev').addEventListener('click',()=>setStep(current-1));
 element.querySelector('.guide-next').addEventListener('click',()=>setStep(current+1));
 select.addEventListener('change',()=>setStep(Number(select.value)));
 element.querySelector('.guide-code').addEventListener('click',event=>{if(event.target.closest('[data-definition]')||window.getSelection()?.toString())return;const fragment=event.target.closest('[data-step]');if(fragment)setStep(Number(fragment.dataset.step));});
 controllerMap.set(element,{guide,setStep,get index(){return current;}});setStep(start);
}
function guideHtml(guide){return `<details class="guide" data-guide="${guide.id}"><summary>Explain this Lean definition</summary><div class="guide-shell"><p class="small">${htmlEscape(guide.introduction)}</p><div class="guide-toolbar"><p class="guide-progress" aria-live="polite"></p><div class="guide-buttons"><button type="button" class="guide-prev">Previous</button><button type="button" class="guide-next">Next</button></div></div><label class="clause-select-label">Choose a clause<select class="clause-select" aria-label="Clause of ${htmlEscape(guide.title)}">${guide.steps.map((step,i)=>`<option value="${i}">${i+1}. ${htmlEscape(step.heading)}</option>`).join('')}</select></label><div class="guide-grid"><pre class="guide-code" aria-label="Selectable Lean clauses"></pre><div class="guide-explanation" aria-live="polite"></div></div><div class="guide-notes">${guide.notes.map(n=>`<p class="small">${htmlEscape(n)}</p>`).join('')}</div></div></details>`;}
function openDefinition(target,opener){
 const id=target.split('.')[0],guide=guideBook.guides.find(g=>g.id===id),definition=guideBook.definitions[id];if(!guide||!definition||!dialog)return;
 if(!dialog.open)returnFocus=opener;
 dialog.querySelector('#dialog-title').textContent=definition.title;
 dialog.querySelector('.dialog-body').innerHTML=`<div class="definition-meaning">${definition.meaning}</div><p class="small">${htmlEscape(definition.provenance)}</p><div class="code-panel"><div class="code-heading"><span>Exact Lean definition</span><a href="${guide.sourceLink}">Source</a></div><div class="code-body"><pre><code>${htmlEscape(guide.source)}</code></pre></div></div>${guideHtml(guide)}<p class="small"><a href="/definitions/#${id}">Read on the Definitions page</a></p>`;
 const element=dialog.querySelector('.guide');const step=guide.steps.findIndex(s=>s.id===target);initialiseGuide(element,Math.max(0,step));
 if(step>=0)element.open=true;
 renderMath(dialog);if(!dialog.open)dialog.showModal();dialog.scrollTop=0;
}
function visitClause(target,opener){
 const id=target.split('.')[0];
 const element=[...document.querySelectorAll('main>.guide, main .definition>.guide')].find(el=>el.dataset.guide===id);
 if(element){const controller=controllerMap.get(element);if(controller){element.open=true;const step=controller.guide.steps.findIndex(s=>s.id===target);controller.setStep(Math.max(0,step));element.scrollIntoView({block:'start'});return true;}}
 if(id!=='theorem-a'){openDefinition(target,opener);return true;}return false;
}
document.addEventListener('click',event=>{
 const term=event.target.closest('[data-definition]');if(term){event.preventDefault();openDefinition(term.dataset.definition,term);return;}
 const link=event.target.closest('[data-guide-link]');if(!link||!guideBook)return;
 const details=link.closest('.guide');const target=link.dataset.guideLink;
 if(details&&details.dataset.guide===target.split('.')[0]){event.preventDefault();const c=controllerMap.get(details);c.setStep(Math.max(0,c.guide.steps.findIndex(s=>s.id===target)));return;}
 if(target.startsWith('theorem-a')){if(visitClause(target,link))event.preventDefault();return;}
 event.preventDefault();openDefinition(target,link);
});
if(dialog){dialog.querySelector('.dialog-close').addEventListener('click',()=>dialog.close());dialog.addEventListener('close',()=>returnFocus?.focus());}
function hashClause(){if(!location.hash.startsWith('#step='))return;const target=decodeURIComponent(location.hash.slice(6));visitClause(target,null);}
fetch('/assets/guides.json').then(response=>{if(!response.ok)throw Error('Guide unavailable');return response.json();}).then(book=>{guideBook=book;document.querySelectorAll('.guide[data-guide]').forEach(el=>initialiseGuide(el));hashClause();window.addEventListener('hashchange',hashClause);}).catch(()=>{document.querySelectorAll('.guide[data-guide] .guide-shell').forEach(el=>{el.innerHTML='<p>The guide could not be loaded. The complete definitions remain available on the Definitions page and in the Lean source.</p>';});});
