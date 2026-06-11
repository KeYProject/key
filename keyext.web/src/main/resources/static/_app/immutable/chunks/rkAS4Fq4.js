var go=Object.defineProperty;var hn=t=>{throw TypeError(t)};var yo=(t,e,n)=>e in t?go(t,e,{enumerable:!0,configurable:!0,writable:!0,value:n}):t[e]=n;var Ee=(t,e,n)=>yo(t,typeof e!="symbol"?e+"":e,n),bo=(t,e,n)=>e.has(t)||hn("Cannot "+n);var Ge=(t,e,n)=>(bo(t,e,"read from private field"),n?n.call(t):e.get(t)),pt=(t,e,n)=>e.has(t)?hn("Cannot add the same private member more than once"):e instanceof WeakSet?e.add(t):e.set(t,n);import{b as Jt,a as p,f as T,t as yt,c as Se,d as Mn}from"./CoTS-PA8.js";import{o as ln,w as wo,g as pn,a as _o}from"./DOHFA51K.js";import{h as he,x as jt,aJ as ko,b as Dn,c as Xt,J as o,a7 as mn,e as Qe,a as nn,aK as So,s as xo,aA as To,aL as jn,ap as cn,aM as Eo,Y as gn,aN as Io,aO as Ao,N as Co,z as Tt,q as mt,at as Po,_ as Oo,a9 as yn,al as Qt,f as gt,ah as Fn,aq as Lo,aP as Be,aQ as qn,ay as No,r as Gn,p as zn,aR as Zt,X as Ft,aS as Ro,aT as Mo,an as Do,m as jo,d as Fo,aj as Un,t as B,w as qo,aU as Go,ar as zo,ak as Uo,o as Ho,aV as Yo,aW as Wo,aX as bn,aY as wn,aZ as Ut,au as Bo,a_ as Ko,a$ as Hn,ae as Yn,b0 as Vo,b1 as Jo,b2 as Xo,b3 as Qo,b4 as Zo,b5 as Wn,b6 as $o,b7 as er,P as Bn,C as Ht,V as dn,G as tr,O as nr,F as ke,b8 as _n,b9 as or,ba as rr,az as ar,bb as sr,Q as X,I as O,i as fe,k as ve,l as v,n as c,B as un,a8 as fn,g as ne,j as b,S as de,bc as Yt,aF as je,bd as ir}from"./B8xKMZX0.js";import{d as ge,a as z,s as W,e as ze}from"./CzhP5laV.js";import{i as H,p as De,b as nt,_ as lr,s as Kn,a as Vn,c as qt}from"./7wWjHvTU.js";import{s as Wt}from"./DcP_HY-I.js";import{B as cr}from"./o-yfdNR1.js";const dr=Symbol("NaN");function Jn(t,e,n){he&&jt();var r=new cr(t),a=!ko();Dn(()=>{var s=e();s!==s&&(s=dr),a&&s!==null&&typeof s=="object"&&(s={}),r.ensure(s,n)})}function Ke(t,e){return e}function ur(t,e,n){for(var r=[],a=e.length,s,i=e.length,h=0;h<a;h++){let k=e[h];zn(k,()=>{if(s){if(s.pending.delete(k),s.done.add(k),s.pending.size===0){var m=t.outrogroups;on(t,cn(s.done)),m.delete(s),m.size===0&&(t.outrogroups=null)}}else i-=1},!1)}if(i===0){var d=r.length===0&&n!==null;if(d){var l=n,u=l.parentNode;Do(u),u.append(l),t.items.clear()}on(t,e,!d)}else s={pending:new Set(e),done:new Set},(t.outrogroups??(t.outrogroups=new Set)).add(s)}function on(t,e,n=!0){var r;if(t.pending.size>0){r=new Set;for(const i of t.pending.values())for(const h of i)r.add(t.items.get(h).e)}for(var a=0;a<e.length;a++){var s=e[a];if(r!=null&&r.has(s)){s.f|=Be;const i=document.createDocumentFragment();jo(s,i)}else Fo(e[a],n)}}var kn;function me(t,e,n,r,a,s=null){var i=t,h=new Map,d=(e&qn)!==0;if(d){var l=t;i=he?Tt(mt(l)):l.appendChild(Xt())}he&&jt();var u=null,k=To(()=>{var D=n();return jn(D)?D:D==null?[]:cn(D)}),m,_=new Map,g=!0;function P(D){(F.effect.f&No)===0&&(F.pending.delete(D),F.fallback=u,fr(F,m,i,e,r),u!==null&&(m.length===0?(u.f&Be)===0?Gn(u):(u.f^=Be,kt(u,null,i)):zn(u,()=>{u=null})))}function f(D){F.pending.delete(D)}var y=Dn(()=>{m=o(k);var D=m.length;let L=!1;if(he){var N=Po(i)===Oo;N!==(D===0)&&(i=yn(),Tt(i),Qt(!1),L=!0)}for(var G=new Set,U=Qe,V=xo(),Y=0;Y<D;Y+=1){he&&gt.nodeType===Fn&&gt.data===Lo&&(i=gt,L=!0,Qt(!1));var x=m[Y],R=r(x,Y),C=g?null:h.get(R);C?(C.v&&mn(C.v,x),C.i&&mn(C.i,Y),V&&U.unskip_effect(C.e)):(C=vr(h,g?i:kn??(kn=Xt()),x,R,Y,a,e,n),g||(C.e.f|=Be),h.set(R,C)),G.add(R)}if(D===0&&s&&!u&&(g?u=nn(()=>s(i)):(u=nn(()=>s(kn??(kn=Xt()))),u.f|=Be)),D>G.size&&So(),he&&D>0&&Tt(yn()),!g)if(_.set(U,G),V){for(const[S,w]of h)G.has(S)||U.skip_effect(w.e);U.oncommit(P),U.ondiscard(f)}else P(U);L&&Qt(!0),o(k)}),F={effect:y,items:h,pending:_,outrogroups:null,fallback:u};g=!1,he&&(i=gt)}function _t(t){for(;t!==null&&(t.f&Ro)===0;)t=t.next;return t}function fr(t,e,n,r,a){var x,R,C,S,w,E,q,j,oe;var s=(r&Mo)!==0,i=e.length,h=t.items,d=_t(t.effect.first),l,u=null,k,m=[],_=[],g,P,f,y;if(s)for(y=0;y<i;y+=1)g=e[y],P=a(g,y),f=h.get(P).e,(f.f&Be)===0&&((R=(x=f.nodes)==null?void 0:x.a)==null||R.measure(),(k??(k=new Set)).add(f));for(y=0;y<i;y+=1){if(g=e[y],P=a(g,y),f=h.get(P).e,t.outrogroups!==null)for(const K of t.outrogroups)K.pending.delete(f),K.done.delete(f);if((f.f&Zt)!==0&&(Gn(f),s&&((S=(C=f.nodes)==null?void 0:C.a)==null||S.unfix(),(k??(k=new Set)).delete(f))),(f.f&Be)!==0)if(f.f^=Be,f===d)kt(f,null,n);else{var F=u?u.next:d;f===t.effect.last&&(t.effect.last=f.prev),f.prev&&(f.prev.next=f.next),f.next&&(f.next.prev=f.prev),Ze(t,u,f),Ze(t,f,F),kt(f,F,n),u=f,m=[],_=[],d=_t(u.next);continue}if(f!==d){if(l!==void 0&&l.has(f)){if(m.length<_.length){var D=_[0],L;u=D.prev;var N=m[0],G=m[m.length-1];for(L=0;L<m.length;L+=1)kt(m[L],D,n);for(L=0;L<_.length;L+=1)l.delete(_[L]);Ze(t,N.prev,G.next),Ze(t,u,N),Ze(t,G,D),d=D,u=G,y-=1,m=[],_=[]}else l.delete(f),kt(f,d,n),Ze(t,f.prev,f.next),Ze(t,f,u===null?t.effect.first:u.next),Ze(t,u,f),u=f;continue}for(m=[],_=[];d!==null&&d!==f;)(l??(l=new Set)).add(d),_.push(d),d=_t(d.next);if(d===null)continue}(f.f&Be)===0&&m.push(f),u=f,d=_t(f.next)}if(t.outrogroups!==null){for(const K of t.outrogroups)K.pending.size===0&&(on(t,cn(K.done)),(w=t.outrogroups)==null||w.delete(K));t.outrogroups.size===0&&(t.outrogroups=null)}if(d!==null||l!==void 0){var U=[];if(l!==void 0)for(f of l)(f.f&Zt)===0&&U.push(f);for(;d!==null;)(d.f&Zt)===0&&d!==t.fallback&&U.push(d),d=_t(d.next);var V=U.length;if(V>0){var Y=(r&qn)!==0&&i===0?n:null;if(s){for(y=0;y<V;y+=1)(q=(E=U[y].nodes)==null?void 0:E.a)==null||q.measure();for(y=0;y<V;y+=1)(oe=(j=U[y].nodes)==null?void 0:j.a)==null||oe.fix()}ur(t,U,Y)}}s&&Ft(()=>{var K,re;if(k!==void 0)for(f of k)(re=(K=f.nodes)==null?void 0:K.a)==null||re.apply()})}function vr(t,e,n,r,a,s,i,h){var d=(i&Io)!==0?(i&Ao)===0?Co(n,!1,!1):gn(n):null,l=(i&Eo)!==0?gn(a):null;return{v:d,i:l,e:nn(()=>(s(e,d??n,l??a,h),()=>{t.delete(r)}))}}function kt(t,e,n){if(t.nodes)for(var r=t.nodes.start,a=t.nodes.end,s=e&&(e.f&Be)===0?e.nodes.start:n;r!==null;){var i=Un(r);if(s.before(r),r===a)return;r=i}}function Ze(t,e,n){e===null?t.effect.first=n:e.next=n,n===null?t.effect.last=e:n.prev=e}function hr(t,e,n=!1,r=!1,a=!1,s=!1){var i=t,h="";if(n){var d=t;he&&(i=Tt(mt(d)))}B(()=>{var l=qo;if(h===(h=e()??"")){he&&jt();return}if(n&&!he){l.nodes=null,d.innerHTML=h,h!==""&&Jt(mt(d),d.lastChild);return}if(l.nodes!==null&&(Go(l.nodes.start,l.nodes.end),l.nodes=null),h!==""){if(he){gt.data;for(var u=jt(),k=u;u!==null&&(u.nodeType!==Fn||u.data!=="");)k=u,u=Un(u);if(u===null)throw zo(),Uo;Jt(gt,k),i=Tt(u);return}var m=r?Yo:a?Wo:void 0,_=Ho(r?"svg":a?"math":"template",m);_.innerHTML=h;var g=r||a?_:_.content;if(Jt(mt(g),g.lastChild),r||a)for(;mt(g);)i.before(mt(g));else i.before(g)}})}const Sn=[...` 	
\r\f \v\uFEFF`];function pr(t,e,n){var r=t==null?"":""+t;if(e&&(r=r?r+" "+e:e),n){for(var a of Object.keys(n))if(n[a])r=r?r+" "+a:a;else if(r.length)for(var s=a.length,i=0;(i=r.indexOf(a,i))>=0;){var h=i+s;(i===0||Sn.includes(r[i-1]))&&(h===r.length||Sn.includes(r[h]))?r=(i===0?"":r.substring(0,i))+r.substring(h+1):i=h}}return r===""?null:r}function mr(t,e){return t==null?null:String(t)}function Ie(t,e,n,r,a,s){var i=t[bn];if(he||i!==n||i===void 0){var h=pr(n,r,s);(!he||h!==t.getAttribute("class"))&&(h==null?t.removeAttribute("class"):t.className=h),t[bn]=n}else if(s&&a!==s)for(var d in s){var l=!!s[d];(a==null||l!==!!a[d])&&t.classList.toggle(d,l)}return s}function et(t,e,n,r){var a=t[wn];if(he||a!==e){var s=mr(e);(!he||s!==t.getAttribute("style"))&&(s==null?t.removeAttribute("style"):t.style.cssText=s),t[wn]=e}return r}function Xn(t,e,n=!1){if(t.multiple){if(e==null)return;if(!jn(e))return Ko();for(var r of t.options)r.selected=e.includes(Et(r));return}for(r of t.options){var a=Et(r);if(Hn(a,e)){r.selected=!0;return}}(!n||e!==void 0)&&(t.selectedIndex=-1)}function gr(t){var e=new MutationObserver(()=>{Xn(t,t.__value)});e.observe(t,{childList:!0,subtree:!0,attributes:!0,attributeFilter:["value"]}),Yn(()=>{e.disconnect()})}function xn(t,e,n=e){var r=new WeakSet,a=!0;Ut(t,"change",s=>{var i=s?"[selected]":":checked",h;if(t.multiple)h=[].map.call(t.querySelectorAll(i),Et);else{var d=t.querySelector(i)??t.querySelector("option:not([disabled])");h=d&&Et(d)}n(h),t.__value=h,Qe!==null&&r.add(Qe)}),Bo(()=>{var s=e();if(t===document.activeElement){var i=Qe;if(r.has(i))return}if(Xn(t,s,a),a&&s===void 0){var h=t.querySelector(":checked");h!==null&&(s=Et(h),n(s))}t.__value=s,a=!1}),gr(t)}function Et(t){return"__value"in t?t.__value:t.value}const yr=Symbol("is custom element"),br=Symbol("is html"),wr=Wn?"link":"LINK",_r=Wn?"progress":"PROGRESS";function xe(t){if(he){var e=!1,n=()=>{if(!e){if(e=!0,t.hasAttribute("value")){var r=t.value;Fe(t,"value",null),t.value=r}if(t.hasAttribute("checked")){var a=t.checked;Fe(t,"checked",null),t.checked=a}}};t[Vo]=n,Ft(n),Jo()}}function kr(t,e){var n=Qn(t);n.value===(n.value=e??void 0)||t.value===e&&(e!==0||t.nodeName!==_r)||(t.value=e??"")}function Fe(t,e,n,r){var a=Qn(t);he&&(a[e]=t.getAttribute(e),e==="src"||e==="srcset"||e==="href"&&t.nodeName===wr)||a[e]!==(a[e]=n)&&(e==="loading"&&(t[$o]=n),n==null?t.removeAttribute(e):typeof n!="string"&&Sr(t).includes(e)?t[e]=n:t.setAttribute(e,n))}function Qn(t){var e;return t[e=Xo]??(t[e]={[yr]:t.nodeName.includes("-"),[br]:t.namespaceURI===Qo})}var Tn=new Map;function Sr(t){var e=t.getAttribute("is")||t.nodeName,n=Tn.get(e);if(n)return n;Tn.set(e,n=[]);for(var r,a=t,s=Element.prototype;s!==a;){r=er(a);for(var i in r)r[i].set&&i!=="innerHTML"&&i!=="textContent"&&i!=="innerText"&&n.push(i);a=Zo(a)}return n}function tt(t,e,n=e){var r=new WeakSet;Ut(t,"input",async a=>{var s=a?t.defaultValue:t.value;if(s=en(t)?tn(s):s,n(s),Qe!==null&&r.add(Qe),await Bn(),s!==(s=e())){var i=t.selectionStart,h=t.selectionEnd,d=t.value.length;if(t.value=s??"",h!==null){var l=t.value.length;i===h&&h===d&&l>d?(t.selectionStart=l,t.selectionEnd=l):(t.selectionStart=i,t.selectionEnd=Math.min(h,l))}}}),(he&&t.defaultValue!==t.value||Ht(e)==null&&t.value)&&(n(en(t)?tn(t.value):t.value),Qe!==null&&r.add(Qe)),dn(()=>{var a=e();if(t===document.activeElement){var s=Qe;if(r.has(s))return}en(t)&&a===tn(t.value)||t.type==="date"&&!a&&!t.value||a!==t.value&&(t.value=a??"")})}const $t=new Set;function St(t,e,n,r,a=r){var s=n.getAttribute("type")==="checkbox",i=t;let h=!1;if(e!==null)for(var d of e)i=i[d]??(i[d]=[]);i.push(n),Ut(n,"change",()=>{var l=n.__value;s&&(l=En(i,l,n.checked)),a(l)},()=>a(s?[]:null)),dn(()=>{var l=r();if(he&&n.defaultChecked!==n.checked){h=!0;return}s?(l=l||[],n.checked=l.includes(n.__value)):n.checked=Hn(n.__value,l)}),Yn(()=>{var l=i.indexOf(n);l!==-1&&i.splice(l,1)}),$t.has(i)||($t.add(i),Ft(()=>{i.sort((l,u)=>l.compareDocumentPosition(u)===4?-1:1),$t.delete(i)})),Ft(()=>{if(h){var l;if(s)l=En(i,l,n.checked);else{var u=i.find(k=>k.checked);l=u==null?void 0:u.__value}a(l)}})}function xr(t,e,n=e){Ut(t,"change",r=>{var a=r?t.defaultChecked:t.checked;n(a)}),(he&&t.defaultChecked!==t.checked||Ht(e)==null)&&n(t.checked),dn(()=>{var r=e();t.checked=!!r})}function En(t,e,n){for(var r=new Set,a=0;a<t.length;a+=1)t[a].checked&&r.add(t[a].__value);return n||r.delete(e),Array.from(r)}function en(t){var e=t.type;return e==="number"||e==="range"}function tn(t){return t===""?null:+t}function Tr(t=!1){const e=tr,n=e.l.u;if(!n)return;let r=()=>rr(e.s);if(t){let a=0,s={};const i=ar(()=>{let h=!1;const d=e.s;for(const l in d)d[l]!==s[l]&&(s[l]=d[l],h=!0);return h&&a++,a});r=()=>o(i)}n.b.length&&nr(()=>{In(e,r),_n(n.b)}),ke(()=>{const a=Ht(()=>n.m.map(or));return()=>{for(const s of a)typeof s=="function"&&s()}}),n.a.length&&ke(()=>{In(e,r),_n(n.a)})}function In(t,e){if(t.l.s)for(const n of t.l.s)o(n);e()}sr();var It;class Er{constructor(){pt(this,It,X("dark"))}get current(){return o(Ge(this,It))}set current(e){O(Ge(this,It),e,!0)}set(e){this.current=e,document.documentElement.dataset.theme=e,localStorage.setItem("theme",e)}toggle(){this.set(this.current==="dark"?"light":"dark")}init(){const e=localStorage.getItem("theme");e==="dark"||e==="light"?this.set(e):this.set(window.matchMedia("(prefers-color-scheme: light)").matches?"light":"dark")}}It=new WeakMap;const Dt=new Er;var Ir=T('<button class="theme-btn svelte-1cmi4dh" title="Toggle theme"> </button>');function Ar(t,e){fe(e,!1),ln(()=>Dt.init()),Tr();var n=Ir(),r=v(n,!0);c(n),B(()=>W(r,Dt.current==="dark"?"☀":"☾")),z("click",n,()=>Dt.toggle()),p(t,n),ve()}ge(["click"]);var Cr=T('<div class="menu svelte-15gydnd"><!></div>');function Pr(t,e){var n=Cr(),r=v(n);Wt(r,()=>e.children??un),c(n),p(t,n)}const Ae=typeof window<"u"&&"__TAURI_INTERNALS__"in window,Or=[{id:"app.preferences",label:"Preferences…",shortcut:"mod+,",menu:{menu:"file",group:4,order:10},run:t=>t.openPreferences()},{id:"app.quit",label:"Quit",shortcut:"mod+Q",menu:{menu:"file",group:5,order:10},visible:()=>Ae,run:t=>t.quit()},{id:"view.toggleTheme",label:"Toggle Theme",shortcut:"mod+T",menu:{menu:"view",group:1,order:10},run:()=>Dt.toggle()}],Lr=Object.freeze(Object.defineProperty({__proto__:null,actions:Or},Symbol.toStringTag,{value:"Module"}));var Nr=T('<span class="spinner svelte-2yth6j">⟳</span> Running…',1),Rr=T('<button class="run-btn svelte-2yth6j"><!></button>');function Mr(t,e){fe(e,!0);let n=X(!1);async function r(){if(!e.ctx.appState.proof||o(n))return;O(n,!0);const d={method:null,nonLinArith:null,maxSteps:1e6,stopMode:null};try{await e.ctx.appState.client.proofAuto(e.ctx.appState.proof,d),e.ctx.appState.proofTreeChanged.notify()}catch(l){e.ctx.reportError(l.toString())}finally{O(n,!1)}}var a=Rr(),s=v(a);{var i=d=>{var l=Nr();fn(),p(d,l)},h=d=>{var l=yt("▶ Auto Proof");p(d,l)};H(s,d=>{o(n)?d(i):d(h,-1)})}c(a),B(()=>a.disabled=!e.ctx.appState.proof||o(n)),z("click",a,r),p(t,a),ve()}ge(["click"]);const Dr={id:"proof.auto",label:"Auto Proof",toolbar:{order:10,component:Mr},enabled:t=>t.appState.proof!==null,run:()=>{}},jr=Object.freeze(Object.defineProperty({__proto__:null,action:Dr},Symbol.toStringTag,{value:"Module"})),Fr='<path d="M2 4.5A1.5 1.5 0 0 1 3.5 3h3.086a1.5 1.5 0 0 1 1.06.44l.915.914A1.5 1.5 0 0 0 9.62 4.8H12.5A1.5 1.5 0 0 1 14 6.3v5.2a1.5 1.5 0 0 1-1.5 1.5h-9A1.5 1.5 0 0 1 2 11.5v-7z"/>',qr='<path stroke-linecap="round" stroke-linejoin="round" d="M2.5 8a5.5 5.5 0 1 1 1.03 3.18"/><path stroke-linecap="round" stroke-linejoin="round" d="M2.5 4.5V8H6"/>',Gr='<rect x="2" y="2" width="12" height="12" rx="1.5"/><rect x="5" y="2" width="6" height="4" rx="0.5" fill="currentColor" stroke="none"/><rect x="4" y="9" width="8" height="5" rx="0.5"/>',zr=[{id:"file.open",label:"Open…",shortcut:"mod+O",icon:Fr,menu:{menu:"file",group:1,order:10},toolbar:{order:20,label:"Open",sep:!0},run:t=>t.files.openPicker()},{id:"file.reopenLast",label:"Reopen Last File",shortcut:"mod+shift+O",icon:qr,menu:{menu:"file",group:1,order:20},toolbar:{order:30,label:"Reopen"},visible:()=>Ae,enabled:t=>t.files.recent.length>0,run:t=>t.files.reopenLast()},{id:"file.recent",label:"Recent Files",menu:{menu:"file",group:2,order:10},visible:t=>Ae&&t.files.recent.length>0,items:t=>t.files.recent.map(e=>({id:e,label:e.split(/[\\/]/).pop()??e,title:e,run:()=>t.files.open(e)})),run:()=>{}},{id:"file.save",label:"Save…",shortcut:"mod+S",icon:Gr,menu:{menu:"file",group:3,order:10},toolbar:{order:40,label:"Save"},visible:t=>t.appState.capabilities.hasSave,enabled:t=>t.appState.proof!==null,run:t=>t.files.saveProof()}],Ur=Object.freeze(Object.defineProperty({__proto__:null,actions:zr},Symbol.toStringTag,{value:"Module"})),Hr={id:"help.about",label:"About KeY-τ…",menu:{menu:"help",group:1,order:10},run:t=>t.openAbout()},Yr=Object.freeze(Object.defineProperty({__proto__:null,action:Hr},Symbol.toStringTag,{value:"Module"})),Wr=[{id:"file",label:"File"},{id:"view",label:"View"},{id:"help",label:"Help"}],Br=Object.assign({"./defs/app-actions.ts":Lr,"./defs/auto-proof.ts":jr,"./defs/file-actions.ts":Ur,"./defs/help-actions.ts":Yr}),vn=Object.values(Br).flatMap(t=>(t.actions??[]).concat(t.action?[t.action]:[])).filter(t=>t!=null);function Kr(t){return vn.filter(e=>{var n;return((n=e.menu)==null?void 0:n.menu)===t}).sort((e,n)=>e.menu.group-n.menu.group||e.menu.order-n.menu.order)}const Vr=vn.filter(t=>t.toolbar).sort((t,e)=>t.toolbar.order-e.toolbar.order),Jr=vn.filter(t=>t.shortcut),rn=typeof navigator<"u"&&(navigator.platform.startsWith("Mac")||navigator.userAgent.includes("Mac OS"));function Xr(t,e){let n=!1,r=!1,a=!1,s=!1,i="";for(const l of e.split("+"))switch(l.toLowerCase()){case"mod":n=!0;break;case"shift":r=!0;break;case"alt":a=!0;break;case"ctrl":s=!0;break;default:i=l.toLowerCase()}const h=rn?t.metaKey:t.ctrlKey,d=rn?t.ctrlKey===s:t.ctrlKey===(s||n);return t.key.toLowerCase()===i&&h===n&&t.shiftKey===r&&t.altKey===a&&d}function Gt(t){const e=t.split("+");return rn?e.map(n=>{switch(n.toLowerCase()){case"mod":return"⌘";case"shift":return"⇧";case"alt":return"⌥";case"ctrl":return"⌃";default:return n.toUpperCase()}}).join(""):e.map(r=>{switch(r.toLowerCase()){case"mod":return"Ctrl";case"shift":return"Shift";case"alt":return"Alt";case"ctrl":return"Ctrl";default:return r.toUpperCase()}}).join("+")}var Qr=T('<div class="menu-backdrop svelte-1elxaub"></div>'),Zr=T('<li class="separator svelte-1elxaub"></li>'),$r=T('<li class="svelte-1elxaub"><button class="dropdown-btn svelte-1elxaub"><span class="menu-label svelte-1elxaub"> </span></button></li>'),ea=T('<li class="menu-section-label svelte-1elxaub"> </li> <!>',1),ta=T('<span class="menu-shortcut svelte-1elxaub"> </span>'),na=T('<li class="svelte-1elxaub"><button class="dropdown-btn svelte-1elxaub"><span class="menu-label svelte-1elxaub"> </span> <!></button></li>'),oa=T("<!> <!>",1),ra=T('<ul class="dropdown svelte-1elxaub"></ul>'),aa=T('<div class="menu-item svelte-1elxaub"><button> </button> <!></div>'),sa=T('<!> <header class="header svelte-1elxaub"><nav class="menu-bar svelte-1elxaub"></nav> <div class="header-right svelte-1elxaub"><!></div></header>',1);function ia(t,e){fe(e,!0);let n=X(null);function r(m){O(n,o(n)===m?null:m,!0)}function a(m){O(n,null),m()}var s=sa(),i=ne(s);{var h=m=>{var _=Qr();z("click",_,()=>O(n,null)),p(m,_)};H(i,m=>{o(n)!==null&&m(h)})}var d=b(i,2),l=v(d);me(l,21,()=>Wr,m=>m.id,(m,_)=>{const g=de(()=>Kr(o(_).id));var P=aa(),f=v(P);let y;var F=v(f,!0);c(f);var D=b(f,2);{var L=N=>{Pr(N,{children:(G,U)=>{var V=ra();me(V,23,()=>o(g),Y=>Y.id,(Y,x,R)=>{var C=Se(),S=ne(C);{var w=q=>{var j=oa(),oe=ne(j);{var K=Z=>{var $=Zr();p(Z,$)};H(oe,Z=>{o(R)>0&&o(x).menu.group!==o(g)[o(R)-1].menu.group&&Z(K)})}var re=b(oe,2);{var ue=Z=>{var $=ea(),ee=ne($),I=v(ee,!0);c(ee);var Q=b(ee,2);me(Q,17,()=>o(x).items(e.ctx),te=>te.id,(te,le)=>{var ce=$r(),se=v(ce),Ue=v(se),He=v(Ue,!0);c(Ue),c(se),c(ce),B(()=>{Fe(se,"title",o(le).title),W(He,o(le).label)}),z("click",se,()=>a(o(le).run)),p(te,ce)}),B(()=>W(I,o(x).label)),p(Z,$)},we=Z=>{var $=na(),ee=v($),I=v(ee),Q=v(I,!0);c(I);var te=b(I,2);{var le=ce=>{var se=ta(),Ue=v(se,!0);c(se),B(He=>W(Ue,He),[()=>Gt(o(x).shortcut)]),p(ce,se)};H(te,ce=>{o(x).shortcut&&ce(le)})}c(ee),c($),B(ce=>{ee.disabled=ce,W(Q,o(x).label)},[()=>{var ce,se;return!(((se=(ce=o(x)).enabled)==null?void 0:se.call(ce,e.ctx))??!0)}]),z("click",ee,()=>a(()=>o(x).run(e.ctx))),p(Z,$)};H(re,Z=>{o(x).items?Z(ue):Z(we,-1)})}p(q,j)},E=de(()=>{var q,j;return((j=(q=o(x)).visible)==null?void 0:j.call(q,e.ctx))??!0});H(S,q=>{o(E)&&q(w)})}p(Y,C)}),c(V),p(G,V)}})};H(D,N=>{o(n)===o(_).id&&N(L)})}c(P),B(()=>{y=Ie(f,1,"menu-btn svelte-1elxaub",null,y,{active:o(n)===o(_).id}),W(F,o(_).label)}),z("click",f,()=>r(o(_).id)),p(m,P)}),c(l);var u=b(l,2),k=v(u);Ar(k,{}),c(u),c(d),p(t,s),ve()}ge(["click"]);var la=T('<button class="reconnect-btn svelte-1piydef"> </button>'),ca=T('<span class="sep svelte-1piydef">·</span> <span class="status-item svelte-1piydef"> </span>',1),da=T('<footer class="status-bar svelte-1piydef"><div class="status-left svelte-1piydef"><div class="server-status svelte-1piydef"><span></span> <span class="status-text svelte-1piydef"> </span> <!></div> <!></div> <div class="status-right svelte-1piydef"><div class="zoom-control svelte-1piydef"><button class="zoom-btn svelte-1piydef" title="Zoom out">−</button>  <span class="zoom-label svelte-1piydef" title="Reset zoom"> </span> <button class="zoom-btn svelte-1piydef" title="Zoom in">+</button> <input class="zoom-slider svelte-1piydef" type="range" min="0.7" max="1.8" step="0.05" title="Zoom"/></div></div></footer>');function ua(t,e){fe(e,!0);const n="key-tau.fontScale",r="keyui.fontScale";let a=X(1);const s=de(()=>Math.round(o(a)*100));function i(S){document.documentElement.style.setProperty("--font-scale",String(S))}function h(S){O(a,Math.max(.7,Math.min(1.8,Math.round(S*20)/20)),!0),localStorage.setItem(n,String(o(a))),i(o(a))}ln(()=>{const S=localStorage.getItem(n)??localStorage.getItem(r),w=S?Number(S):1;O(a,Number.isFinite(w)?w:1,!0),i(o(a))});const d={connected:"Server connected",connecting:"Connecting…",disconnected:"Server disconnected"};let l=X(!1);ke(()=>{if(e.appState.serverStatus!=="disconnected")return;const S=e.appState.client.config;if(!Ae||S.type==="websocket"){O(l,!0);return}if(S.type==="local-stdin"){O(l,!1);return}const w=S.type==="tcp"?S.host:"localhost",E=S.port;let q=!1;const j=async()=>{try{const K=await e.appState.client.probeTcp(w,E);q||O(l,K,!0)}catch{}};j();const oe=setInterval(j,3e3);return()=>{q=!0,clearInterval(oe)}});const u=de(()=>o(l)?"Reconnect":"Start Server");function k(){e.onReconnect(e.appState.client.config)}var m=da(),_=v(m),g=v(_),P=v(g),f=b(P,2),y=v(f,!0);c(f);var F=b(f,2);{var D=S=>{var w=la(),E=v(w,!0);c(w),B(()=>W(E,o(u))),z("click",w,k),p(S,w)};H(F,S=>{e.appState.serverStatus==="disconnected"&&S(D)})}c(g);var L=b(g,2);{var N=S=>{var w=ca(),E=b(ne(w),2),q=v(E,!0);c(E),B(()=>W(q,e.appState.proof.proofId)),p(S,w)};H(L,S=>{e.appState.proof&&S(N)})}c(_);var G=b(_,2),U=v(G),V=v(U),Y=b(V,2),x=v(Y);c(Y);var R=b(Y,2),C=b(R,2);xe(C),c(U),c(G),c(m),B(()=>{Fe(g,"title",d[e.appState.serverStatus]??e.appState.serverStatus),Ie(P,1,`dot dot-${e.appState.serverStatus??""}`,"svelte-1piydef"),W(y,d[e.appState.serverStatus]??e.appState.serverStatus),W(x,`${o(s)??""}%`),kr(C,o(a))}),z("click",V,()=>h(o(a)-.05)),z("click",Y,()=>h(1)),z("click",R,()=>h(o(a)+.05)),z("input",C,S=>h(Number(S.target.value))),p(t,m),ve()}ge(["click","input"]);function fa(t,e=!1){return window.__TAURI_INTERNALS__.transformCallback(t,e)}async function ot(t,e={},n){return window.__TAURI_INTERNALS__.invoke(t,e,n)}const va={id:"key-java",label:"KeY (Java backend)",description:"Standard KeY prover for Java programs.",order:2,capabilities:{hasTermSpans:!0,hasTacletInfo:!0,hasSave:!0,hasScriptMacro:!0}},ha=Object.freeze(Object.defineProperty({__proto__:null,backend:va},Symbol.toStringTag,{value:"Module"})),pa={id:"key-rust",label:"RustyKeY",description:"KeY prover for Rust programs.",order:1,capabilities:{hasTermSpans:!0,hasTacletInfo:!0,hasSave:!0,hasScriptMacro:!0}},ma=Object.freeze(Object.defineProperty({__proto__:null,backend:pa},Symbol.toStringTag,{value:"Module"})),ga={id:"keyther-solidity",label:"KeYther (Solidity)",description:"KeY prover for Solidity smart contracts",order:3,capabilities:{hasTermSpans:!0,hasTacletInfo:!0,hasSave:!0,hasScriptMacro:!1}},ya=Object.freeze(Object.defineProperty({__proto__:null,backend:ga},Symbol.toStringTag,{value:"Module"})),ba=Object.assign({"./defs/key-java.ts":ha,"./defs/key-rust.ts":ma,"./defs/keyther-solidity.ts":ya}),an=Object.values(ba).map(t=>t.backend).filter(t=>t!=null).sort((t,e)=>(t.order??99)-(e.order??99));function sn(t){return an.find(e=>e.id===t)??an[0]}function An(t,e){return{jsonrpc:"2.0",id:null,error:{code:t,message:e}}}class wa{constructor(){Ee(this,"ws",null);Ee(this,"nextId",0);Ee(this,"inflight",new Map);Ee(this,"onClose",null)}connect(e){return new Promise((n,r)=>{let a=!1;const s=new WebSocket(e);s.onopen=()=>{a=!0,n()},s.onclose=()=>{var i;for(const h of this.inflight.values())h(An(-32001,"Server connection lost"));this.inflight.clear(),a?(i=this.onClose)==null||i.call(this):r(new Error(`Could not connect to ${e}`))},s.onmessage=i=>{let h;try{h=JSON.parse(i.data)}catch{return}if(h&&typeof h.id=="number"){const d=this.inflight.get(h.id);d&&(this.inflight.delete(h.id),d(h))}},this.ws=s})}sendMsg(e,n){if(!this.ws||this.ws.readyState!==WebSocket.OPEN)return Promise.resolve(An(-32e3,"Server not connected"));const r=this.nextId++;return new Promise(a=>{this.inflight.set(r,a),this.ws.send(JSON.stringify({jsonrpc:"2.0",id:r,method:e,params:n}))})}close(){var e;this.onClose=null,(e=this.ws)==null||e.close(),this.ws=null}}function _a(t){switch(t.type){case"websocket":return t.url;case"tcp":return`ws://${t.host}:${t.port}`;case"local-tcp":return`ws://localhost:${t.port}`;case"local-stdin":return"ws://localhost:6789"}}class ka{constructor(){Ee(this,"_flavor","key-rust");Ee(this,"_config",{type:"local-tcp",port:6789});Ee(this,"_jarPath",null);Ee(this,"_serverStarted",!1);Ee(this,"_ws",null);Ee(this,"onStatusChange",null)}get usesWebSocket(){return!Ae||this._config.type==="websocket"}_setStatus(e){var n;(n=this.onStatusChange)==null||n.call(this,e)}get config(){return this._config}get jarPath(){return this._jarPath}setFlavor(e){this._flavor=e}get capabilities(){return sn(this._flavor).capabilities}async connect(e,n){this._config=e,this._jarPath=n??null,this._serverStarted=!1,this.usesWebSocket||e.type==="tcp"||n?await this.ensureServerStarted():this._setStatus("disconnected")}async ensureServerStarted(){if(!this._serverStarted){if(this.usesWebSocket){await this.connectWebSocket();return}if(this._config.type!=="tcp"&&!this._jarPath)throw new Cn("No server JAR configured. Select api.jar in Preferences → Backend.");this._setStatus("connecting");try{await ot("connect",{config:this._config,jarPath:this._jarPath??null}),this._serverStarted=!0,this._setStatus("connected")}catch(e){throw this._setStatus("disconnected"),e}}}async connectWebSocket(){var n;(n=this._ws)==null||n.close();const e=new wa;e.onClose=()=>{this._ws===e&&(this._serverStarted=!1,this._setStatus("disconnected"))},this._setStatus("connecting");try{await e.connect(_a(this._config)),this._ws=e,this._serverStarted=!0,this._setStatus("connected")}catch(r){throw this._setStatus("disconnected"),r}}async probeTcp(e,n){return Ae?await ot("probe_tcp",{host:e,port:n}):!1}async send(e,n){var a;const r=this.usesWebSocket?await(((a=this._ws)==null?void 0:a.sendMsg(e,n))??Promise.resolve({error:{code:-32e3,message:"Server not connected"}})):await ot("send_msg",{method:e,params:n});if(r.error){const s=new Cn;throw s.code=r.error.code,s.data=r.error.data??"",s.message=r.error.message,s.method=e,s.isConnectionError()&&(this._serverStarted=!1,this._setStatus("disconnected")),s}return r.result}async version(){return await this.send("meta/version",null)}async load(e){await this.ensureServerStarted();let n={problemFile:{uri:e.problemFile},$class:"org.keyproject.key.api.data.LoadParams"};return e.includes&&(n.includes=e.includes.map(r=>({uri:r}))),await this.send("loading/load",n)}async loadKey(e){return await this.send("loading/loadKey",e)}async proofTreeRoot(e){return await this.send("proofTree/root",e)}async proofList(){const e=await this.send("proof/list",null);return Array.isArray(e)?e:[]}async proofTreeChildren(e,n){let r={id:n.nodeId,$class:"org.keyproject.key.api.data.KeyIdentifications$TreeNodeId"};return await this.send("proofTree/children",[e,r])}async goalPrint(e,n){return await this.send("goal/print",[e,n])}async proofGoals(e,n,r){const a=await this.send("proof/goals",[e,n,r]),s=Array.isArray(a)?a:a?[a]:[],i=h=>({nodeId:h.nodeId??h.nodeid,branchLabel:h.branchLabel??"",scriptRuleApplication:h.scriptRuleApplication??!1,children:(h.children??[]).map(i),description:h.description??""});return s.map(i)}async proofAuto(e,n){let r=n;return r.$class="org.keyproject.key.api.data.StrategyOptions",await this.send("proof/auto",[e,r])}async proofPruneTo(e){return await this.send("proof/pruneTo",[e])}async goalActions(e,n){return await this.send("goal/actions",[e,n])}async goalFreePrint(e){await this.send("goal/free",[e])}async applyAction(e){return await this.send("goal/apply_action",[e])}async saveProof(e,n){return await this.send("proof/save",[e,n])}async disposeEnv(e){return await this.send("env/dispose",[e])}}class Cn extends Error{constructor(){super(...arguments);Ee(this,"code",0);Ee(this,"data","");Ee(this,"method","")}isConnectionError(){return this.code===-32e3||this.code===-32001}userMessage(){return this.code===-32e3?"Server is not running. Open a proof file to start it.":this.code===-32001?"Lost connection to the server.":this.message?this.message:"An unknown server error occurred."}toString(){const n=this.method?` (${this.method})`:"",r=this.data?`
${this.data}`:"";return`${this.userMessage()}${n}${r}`}}var xt=(t=>(t[t.Builtin=0]="Builtin",t[t.Script=1]="Script",t[t.Macro=2]="Macro",t[t.Taclet=3]="Taclet",t))(xt||{}),Sa=T('<div class="panel svelte-hxsa5u"><!></div>');function Zn(t,e){var n=Sa(),r=v(n);Wt(r,()=>e.children??un),c(n),p(t,n)}var xa=T('<div class="backdrop svelte-ta60gp" role="presentation"><div class="modal svelte-ta60gp" role="dialog" aria-modal="true" tabindex="-1"><button class="close svelte-ta60gp">×</button> <!></div></div>');function zt(t,e){fe(e,!0);let n=De(e,"closeOnBackdrop",3,!0);function r(){n()&&e.onclose()}function a(d){d.key==="Escape"&&e.onclose()}var s=Se();ze("keydown",Yt,a);var i=ne(s);{var h=d=>{var l=xa(),u=v(l),k=v(u),m=b(k,2);Wt(m,()=>e.children),c(u),c(l),z("click",l,r),z("click",u,_=>_.stopPropagation()),z("click",k,function(..._){var g;(g=e.onclose)==null||g.apply(this,_)}),p(d,l)};H(i,d=>{e.open&&d(h)})}p(t,s),ve()}ge(["click"]);const Pn=[{label:"System",value:"system-ui, -apple-system, sans-serif"},{label:"Monospace",value:"ui-monospace, monospace"},{label:"JetBrains Mono",value:"'JetBrains Mono', monospace"},{label:"Fira Code",value:"'Fira Code', monospace"},{label:"Cascadia Code",value:"'Cascadia Code', monospace"},{label:"Menlo",value:"Menlo, monospace"},{label:"Consolas",value:"Consolas, monospace"}],Ta={useOverride:!1,font:{family:"system-ui, -apple-system, sans-serif",size:13}},ut={connection:{type:"local-tcp",port:6789},flavor:"key-rust",jarPaths:{},fonts:{global:{family:"system-ui, -apple-system, sans-serif",size:14},panes:{tree:{useOverride:!0,font:{family:"system-ui, -apple-system, sans-serif",size:13}},sequent:{useOverride:!0,font:{family:"monospace",size:14}}}}},$n="key-tau.preferences",Ea="keyui.preferences";function Ia(){try{const t=localStorage.getItem($n)??localStorage.getItem(Ea);if(t){const e=JSON.parse(t);return{...ut,...e,flavor:e.flavor??ut.flavor,connection:Ca(e.connection),jarPaths:{...e.jarPaths??{}},fonts:Aa(e.fonts)}}}catch{}return structuredClone(ut)}function Aa(t){if(!t||typeof t!="object")return structuredClone(ut.fonts);const e={...ut.fonts.global,...t.global??{}},n={};if(t.panes&&typeof t.panes=="object")for(const[r,a]of Object.entries(t.panes))n[r]=a;else for(const[r,a]of Object.entries(t))r!=="global"&&a&&typeof a=="object"&&"useOverride"in a&&(n[r]=a);return{global:e,panes:n}}function Ca(t){return!t||typeof t!="object"?ut.connection:t.type==="local"?{type:"local-tcp",port:t.port??6789}:t.type==="local-stdin"?{type:"local-stdin"}:t.type==="local-tcp"?{type:"local-tcp",port:t.port??6789}:t.type==="tcp"?{type:"tcp",host:t.host??"localhost",port:t.port??6789}:t.type==="websocket"?{type:"websocket",url:t.url??"ws://localhost:6790"}:ut.connection}const bt=wo(Ia());bt.subscribe(t=>{try{localStorage.setItem($n,JSON.stringify(t))}catch{}});function Pa(t,e){const n=t.fonts.panes[e];return n!=null&&n.useOverride?n.font:t.fonts.global}async function eo(t={}){return typeof t=="object"&&Object.freeze(t),await ot("plugin:dialog|open",{options:t})}async function Oa(t={}){return typeof t=="object"&&Object.freeze(t),await ot("plugin:dialog|save",{options:t})}var La=T('<span class="jar-path svelte-m59myo"> </span> <button class="jar-btn svelte-m59myo">Change…</button> <button class="jar-btn jar-clear svelte-m59myo" title="Remove JAR">✕</button>',1),Na=T('<span class="jar-none svelte-m59myo">none</span> <button class="jar-btn jar-set svelte-m59myo">Select JAR…</button>',1),Ra=T('<div class="jar-row svelte-m59myo"><span class="jar-label svelte-m59myo">Server JAR</span> <!></div>'),Ma=T('<label><input type="radio" name="flavor"/> <div class="opt-body"><span class="opt-name"> </span> <span class="opt-desc"> </span> <!></div></label>'),Da=T('<h3 class="section-label">Backend Type</h3> <p class="hint">Choose which prover backend this UI will connect to.</p> <div class="options"></div>',1);function ja(t,e){fe(e,!0);const n=[];let r=De(e,"draft",7);function a(l){return l.split(/[\\/]/).pop()??l}async function s(l){const u=await eo({multiple:!1,directory:!1,filters:[{name:"Java Archive",extensions:["jar"]},{name:"All Files",extensions:["*"]}],title:"Select server JAR"});u!=null&&(r().jarPaths[l]=u)}function i(l){r().jarPaths[l]=""}var h=Da(),d=b(ne(h),4);me(d,21,()=>an,Ke,(l,u)=>{const k=de(()=>r().jarPaths[o(u).id]??"");var m=Ma();let _;var g=v(m);xe(g);var P,f=b(g,2),y=v(f),F=v(y,!0);c(y);var D=b(y,2),L=v(D,!0);c(D);var N=b(D,2);{var G=U=>{var V=Ra(),Y=b(v(V),2);{var x=C=>{var S=La(),w=ne(S),E=v(w,!0);c(w);var q=b(w,2),j=b(q,2);B(oe=>{Fe(w,"title",o(k)),W(E,oe)},[()=>a(o(k))]),z("click",q,()=>s(o(u).id)),z("click",j,()=>i(o(u).id)),p(C,S)},R=C=>{var S=Na(),w=b(ne(S),2);z("click",w,()=>s(o(u).id)),p(C,S)};H(Y,C=>{o(k)?C(x):C(R,-1)})}c(V),z("click",V,C=>C.preventDefault()),p(U,V)};H(N,U=>{Ae&&r().flavor===o(u).id&&U(G)})}c(f),c(m),B(()=>{_=Ie(m,1,"option svelte-m59myo",null,_,{selected:r().flavor===o(u).id}),P!==(P=o(u).id)&&(g.value=(g.__value=o(u).id)??""),W(F,o(u).label),W(L,o(u).description)}),St(n,[],g,()=>(o(u).id,r().flavor),U=>r().flavor=U),p(l,m)}),c(d),p(t,h),ve()}ge(["click"]);const Fa={id:"backend",label:"Backend",icon:"◈",order:10,component:ja,createDraft:t=>({flavor:t.flavor,jarPaths:{...t.jarPaths??{}}}),applyDraft:(t,e)=>({...e,flavor:t.flavor,jarPaths:{...e.jarPaths??{},...t.jarPaths}})},qa=Object.freeze(Object.defineProperty({__proto__:null,section:Fa},Symbol.toStringTag,{value:"Module"}));var Ga=T(`<p class="hint">Running in a browser: only WebSocket connections are available
        (start the server with <code>--websocket</code>).</p>`),za=T('<div class="inline-field svelte-1qe2zza"><label for="p-local-port" class="svelte-1qe2zza">Port</label> <input id="p-local-port" type="number" class="input port-input svelte-1qe2zza" min="1" max="65535" placeholder="6789"/></div>'),Ua=T('<div class="inline-fields svelte-1qe2zza"><div class="inline-field wide svelte-1qe2zza"><label for="p-host" class="svelte-1qe2zza">Host</label> <input id="p-host" type="text" class="input" placeholder="localhost" spellcheck="false"/></div> <div class="inline-field svelte-1qe2zza"><label for="p-tcp-port" class="svelte-1qe2zza">Port</label> <input id="p-tcp-port" type="number" class="input port-input svelte-1qe2zza" min="1" max="65535" placeholder="6789"/></div></div>'),Ha=T(`<label class="option"><input type="radio" name="conn"/> <div class="opt-body"><span class="opt-name">Local server — stdin</span> <span class="opt-desc">Spawn the JAR (<code>--std</code>) and communicate over stdin/stdout.
                Configure the JAR for each backend in the <strong>Backend</strong> tab.</span></div></label> <label class="option"><input type="radio" name="conn"/> <div class="opt-body"><span class="opt-name">Local server — TCP</span> <span class="opt-desc">Spawn the JAR (<code>--server PORT</code>) and connect via TCP on localhost.
                Preferred: survives UI restarts without restarting the server.</span> <!></div></label> <label class="option"><input type="radio" name="conn"/> <div class="opt-body"><span class="opt-name">External TCP server</span> <span class="opt-desc">Connect to an already-running server (e.g. started manually with <code>--server PORT</code>).
                No JAR needed.</span> <!></div></label>`,1),Ya=T('<div class="inline-field svelte-1qe2zza"><label for="p-ws-url" class="svelte-1qe2zza">URL</label> <input id="p-ws-url" type="text" class="input" placeholder="ws://localhost:6790" spellcheck="false"/></div>'),Wa=T(`<h3 class="section-label">Server Connection</h3> <!> <div class="options"><!> <label class="option"><input type="radio" name="conn"/> <div class="opt-body"><span class="opt-name">WebSocket server</span> <span class="opt-desc">Connect to a server started with <code>--websocket</code>.
                The only mode available from a browser.</span> <!></div></label></div>`,1);function Ba(t,e){fe(e,!0);const n=[];let r=De(e,"draft",7);var a=Wa(),s=b(ne(a),2);{var i=P=>{var f=Ga();p(P,f)};H(s,P=>{Ae||P(i)})}var h=b(s,2),d=v(h);{var l=P=>{var f=Ha(),y=ne(f),F=v(y);xe(F),F.value=F.__value="local-stdin",fn(2),c(y);var D=b(y,2),L=v(D);xe(L),L.value=L.__value="local-tcp";var N=b(L,2),G=b(v(N),4);{var U=S=>{var w=za(),E=b(v(w),2);xe(E),c(w),z("click",w,q=>q.preventDefault()),tt(E,()=>r().localPort,q=>r().localPort=q),p(S,w)};H(G,S=>{r().mode==="local-tcp"&&S(U)})}c(N),c(D);var V=b(D,2),Y=v(V);xe(Y),Y.value=Y.__value="tcp";var x=b(Y,2),R=b(v(x),4);{var C=S=>{var w=Ua(),E=v(w),q=b(v(E),2);xe(q),c(E);var j=b(E,2),oe=b(v(j),2);xe(oe),c(j),c(w),z("click",w,K=>K.preventDefault()),tt(q,()=>r().host,K=>r().host=K),tt(oe,()=>r().tcpPort,K=>r().tcpPort=K),p(S,w)};H(R,S=>{r().mode==="tcp"&&S(C)})}c(x),c(V),St(n,[],F,()=>r().mode,S=>r().mode=S),St(n,[],L,()=>r().mode,S=>r().mode=S),St(n,[],Y,()=>r().mode,S=>r().mode=S),p(P,f)};H(d,P=>{Ae&&P(l)})}var u=b(d,2),k=v(u);xe(k),k.value=k.__value="websocket";var m=b(k,2),_=b(v(m),4);{var g=P=>{var f=Ya(),y=b(v(f),2);xe(y),c(f),z("click",f,F=>F.preventDefault()),tt(y,()=>r().wsUrl,F=>r().wsUrl=F),p(P,f)};H(_,P=>{r().mode==="websocket"&&P(g)})}c(m),c(u),c(h),St(n,[],k,()=>r().mode,P=>r().mode=P),p(t,a),ve()}ge(["click"]);const to="ws://localhost:6790";function Ka(t){const e={mode:"local-tcp",host:"localhost",tcpPort:6789,localPort:6789,wsUrl:to};switch(t.type){case"tcp":return{...e,mode:"tcp",host:t.host,tcpPort:t.port};case"local-tcp":return{...e,mode:"local-tcp",localPort:t.port};case"local-stdin":return{...e,mode:"local-stdin"};case"websocket":return{...e,mode:"websocket",wsUrl:t.url}}}function Va(t){switch(t.mode){case"tcp":return{type:"tcp",host:t.host.trim()||"localhost",port:Number(t.tcpPort)||6789};case"local-tcp":return{type:"local-tcp",port:Number(t.localPort)||6789};case"websocket":return{type:"websocket",url:t.wsUrl.trim()||to};case"local-stdin":return{type:"local-stdin"}}}const Ja={id:"connection",label:"Connection",icon:"⇌",order:20,component:Ba,createDraft:t=>Ka(t.connection),applyDraft:(t,e)=>({...e,connection:Va(t)})},Xa=Object.freeze(Object.defineProperty({__proto__:null,section:Ja},Symbol.toStringTag,{value:"Module"}));var Qa=T('<div class="loading svelte-1w5cybu">Loading…</div>'),Za=T('<div class="empty svelte-1w5cybu">No open goals found.</div>'),$a=T('<li><button class="goal-btn svelte-1w5cybu"><span class="goal-id svelte-1w5cybu"> </span> <span class="goal-text svelte-1w5cybu"> </span></button></li>'),es=T('<ul class="goal-list svelte-1w5cybu"></ul>'),ts=T('<div class="summary svelte-1w5cybu"> </div> <!>',1),ns=T('<h3 class="svelte-1w5cybu">Goals</h3> <!>',1);function os(t,e){fe(e,!0);let n=De(e,"appState",7),r=X(je([])),a=X(!1),s=X(je({}));const i=80;function h(f){const y=f.replace(/\s+/g," ").trim();return y.length>i?y.slice(0,i-1)+"…":y}async function d(f){const y={};for(const F of f)try{const D=await n().client.goalPrint(F.nodeId,{unicode:!1,width:1e4,indentation:0,pure:!0,termLabels:!1});y[F.nodeId.nodeId]=h(D.sequent),n().client.goalFreePrint(D.id).catch(()=>{})}catch{}O(s,y,!0)}function l(f){return f.children.length===0?[f]:f.children.flatMap(l)}async function u(){if(!n().proof){O(r,[],!0);return}O(a,!0);try{const f=await n().client.proofGoals(n().proof,!0,!1);O(r,f.flatMap(l),!0),d(o(r))}catch(f){console.error("GoalsPanel: failed to load goals",f),O(r,[],!0)}finally{O(a,!1)}}ke(()=>{n().proofTreeChanged.count,u()});function k(f){n().active_node=f}var m=ns(),_=b(ne(m),2);{var g=f=>{var y=Qa();p(f,y)},P=f=>{var y=ts(),F=ne(y),D=v(F);c(F);var L=b(F,2);{var N=U=>{var V=Za();p(U,V)},G=U=>{var V=es();me(V,21,()=>o(r),Ke,(Y,x)=>{var R=$a(),C=v(R),S=v(C),w=v(S);c(S);var E=b(S,2),q=v(E,!0);c(E),c(C),c(R),B(()=>{Fe(C,"title",o(s)[o(x).nodeId.nodeId]??""),W(w,`#${o(x).nodeId.nodeId??""}`),W(q,o(s)[o(x).nodeId.nodeId]||"Open Goal")}),z("click",C,()=>k(o(x).nodeId)),p(Y,R)}),c(V),p(U,V)};H(L,U=>{o(r).length===0?U(N):U(G,-1)})}B(()=>W(D,`Open goals: ${o(r).length??""}`)),p(f,y)};H(_,f=>{o(a)?f(g):f(P,-1)})}p(t,m),ve()}ge(["click"]);const rs={id:"goals",label:"Goals",order:30,defaultFlex:2,minWidth:120,component:os},as=Object.freeze(Object.defineProperty({__proto__:null,pane:rs},Symbol.toStringTag,{value:"Module"}));var ss=T('<div class="ctx-backdrop svelte-192vamk"><div class="ctx-menu svelte-192vamk"><!></div></div>');function no(t,e){fe(e,!0);let n=X(null),r=X(0),a=X(0);ke(()=>{if(!e.open)return;const l=e.positionX,u=e.positionY;O(r,u,!0),O(a,l,!0),Bn().then(()=>{if(!o(n))return;const k=o(n).getBoundingClientRect();k.right>window.innerWidth&&O(a,l-k.width),k.bottom>window.innerHeight&&O(r,u-k.height)})});function s(l){l.key==="Escape"&&e.onClose()}var i=Se();ze("keydown",Yt,s);var h=ne(i);{var d=l=>{var u=ss(),k=v(u),m=v(k);Wt(m,()=>e.children??un),c(k),nt(k,_=>O(n,_),()=>o(n)),c(u),B(()=>et(k,`top:${o(r)??""}px; left:${o(a)??""}px;`)),z("click",u,function(..._){var g;(g=e.onClose)==null||g.apply(this,_)}),z("click",k,_=>_.stopPropagation()),p(l,u)};H(h,l=>{e.open&&l(d)})}p(t,i),ve()}ge(["click"]);var is=T('<div class="ctx-simple svelte-1wbs0gg">A closed goal</div>'),ls=T('<div class="ctx-mono loading svelte-1wbs0gg">Loading…</div>'),cs=T('<div class="ctx-mono error svelte-1wbs0gg"> </div>'),On=T('<div class="ctx-mono svelte-1wbs0gg"> </div>'),ds=T('<div class="ctx-title svelte-1wbs0gg">Taclet info</div> <div class="ctx-content svelte-1wbs0gg"><div class="ctx-row svelte-1wbs0gg"><div class="ctx-label svelte-1wbs0gg">Rule</div> <div class="ctx-value svelte-1wbs0gg"> </div></div> <div class="ctx-sep svelte-1wbs0gg"></div> <div class="ctx-label svelte-1wbs0gg">Applied on</div> <!> <div class="ctx-sep svelte-1wbs0gg"></div> <!></div>',1);function us(t,e){fe(e,!0);let n=je({loading:!0,sequent:null,taclet:null,error:null});ke(()=>{if(e.nodeId==null)return;n.loading=!0,n.sequent=null,n.taclet=null,n.error=null;const d={unicode:!1,width:120,indentation:0,pure:!1,termLabels:!0};e.appState.client.goalPrint(e.nodeId,d).then(l=>{n.loading=!1,n.sequent=l.sequent,n.taclet=l.tacletAppInfo}).catch(l=>{n.loading=!1,n.error=l.toString()})});var r=Se(),a=ne(r);{var s=d=>{var l=is();p(d,l)},i=de(()=>{var d;return((d=e.nodeName)==null?void 0:d.toLowerCase())==="closed goal"}),h=d=>{var l=ds(),u=b(ne(l),2),k=v(u),m=b(v(k),2),_=v(m,!0);c(m),c(k);var g=b(k,6);{var P=L=>{var N=ls();p(L,N)},f=L=>{var N=cs(),G=v(N,!0);c(N),B(()=>W(G,n.error)),p(L,N)},y=L=>{var N=On(),G=v(N,!0);c(N),B(()=>W(G,n.sequent??"-")),p(L,N)};H(g,L=>{n.loading?L(P):n.error?L(f,1):L(y,-1)})}var F=b(g,4);{var D=L=>{var N=On(),G=v(N,!0);c(N),B(()=>W(G,n.taclet)),p(L,N)};H(F,L=>{n.taclet!=null&&L(D)})}c(u),B(()=>W(_,e.nodeName??"-")),p(d,l)};H(a,d=>{o(i)?d(s):d(h,-1)})}p(t,r),ve()}function fs(){const t={id:"tab-0",nodeId:null,label:"Sequent"};return[{id:"col-0",tabs:[t],activeTabId:t.id,flex:1}]}var At;class vs{constructor(){pt(this,At,X(je(fs())))}get columns(){return o(Ge(this,At))}set columns(e){O(Ge(this,At),e,!0)}openInTab(e,n,r){const a=this.columns[0],s={id:`tab-${Date.now()}`,nodeId:e,label:n,nodeStatus:r};a.tabs.push(s),a.activeTabId=s.id}openInSplit(e,n,r){const a={id:`tab-${Date.now()}`,nodeId:e,label:n,nodeStatus:r},s=this.columns[this.columns.length-1],i=s.flex/2;s.flex=i,this.columns.push({id:`col-${Date.now()}`,tabs:[a],activeTabId:a.id,flex:i})}resizeColumns(e,n,r){if(r===0||n===0)return;const a=this.columns,s=a[e],i=a[e+1];if(!s||!i)return;const h=a.reduce((k,m)=>k+m.flex,0),d=n/r*h,l=h/a.length*.1,u=s.flex+i.flex;s.flex=Math.max(l,Math.min(s.flex+d,u-l)),i.flex=u-s.flex}closeTab(e,n){const r=this.columns.findIndex(i=>i.id===e);if(r===-1)return;const a=this.columns[r];if(a.tabs.length===1){this.removeColumn(r);return}const s=a.tabs.findIndex(i=>i.id===n);s!==-1&&(a.tabs.splice(s,1),a.activeTabId===n&&(a.activeTabId=a.tabs[Math.min(s,a.tabs.length-1)].id))}closeColumn(e){const n=this.columns.findIndex(r=>r.id===e);n!==-1&&this.removeColumn(n)}setActiveTab(e,n){const r=this.columns.find(a=>a.id===e);r&&(r.activeTabId=n)}removeColumn(e){if(this.columns.length<=1)return;const[n]=this.columns.splice(e,1),r=this.columns[Math.min(e,this.columns.length-1)];r&&(r.flex+=n.flex)}}At=new WeakMap;const $e=new vs;var hs=T('<button class="clear-btn svelte-1u5swoa">✕</button>'),ps=T('<div class="loading-banner svelte-1u5swoa">Loading proof tree…</div>'),ms=T('<div class="empty-msg svelte-1u5swoa">No matching nodes</div>'),gs=T('<button><span></span> <span class="node-label svelte-1u5swoa"><span class="node-id svelte-1u5swoa"> </span> </span></button>'),ys=T('<div class="search-results svelte-1u5swoa"><!></div>'),bs=T('<span class="toggle-placeholder svelte-1u5swoa"></span>'),ws=T('<span class="spinner svelte-1u5swoa">⟳</span>'),_s=T('<button class="toggle-btn svelte-1u5swoa"><!></button>'),ks=T('<div class="indent svelte-1u5swoa"></div> <!> <button><span></span> <span class="node-label svelte-1u5swoa"><span class="node-id svelte-1u5swoa"> </span> </span></button>',1),Ss=T('<div class="indent svelte-1u5swoa"></div> <div class="branch-marker svelte-1u5swoa"><span class="branch-icon svelte-1u5swoa">⑂</span> </div>',1),xs=T('<div class="row svelte-1u5swoa"><!></div>'),Ts=T('<div class="virtual-list svelte-1u5swoa"><div></div></div>'),Es=T('<div class="scroll-viewport svelte-1u5swoa"><!></div>'),Is=T('<span class="taclet-hint svelte-1u5swoa"> </span>'),As=T('<div class="taclet-empty svelte-1u5swoa">Hover a node to see its info</div>'),Cs=T('<div class="taclet-content svelte-1u5swoa"><!></div>'),Ps=T('<div class="ctx-error-msg svelte-1u5swoa"> </div>'),Os=T('<div class="ctx-menu svelte-1u5swoa"><div class="ctx-section-label svelte-1u5swoa"> </div> <div class="ctx-divider svelte-1u5swoa"></div> <button class="ctx-action svelte-1u5swoa"><span class="ctx-icon svelte-1u5swoa">✂</span> <span> </span></button> <!> <div class="ctx-divider svelte-1u5swoa"></div> <button class="ctx-action svelte-1u5swoa"><span class="ctx-icon svelte-1u5swoa">⊕</span> <span>Open in New Tab</span></button> <button class="ctx-action svelte-1u5swoa"><span class="ctx-icon svelte-1u5swoa">⧉</span> <span>Open in New Split</span></button></div>'),Ls=T('<div class="tree-container svelte-1u5swoa"><div class="tree-header svelte-1u5swoa"><h3 class="svelte-1u5swoa">Proof Tree</h3> <span class="node-count svelte-1u5swoa"> </span></div> <div class="search-row svelte-1u5swoa"><input type="text" class="search-input svelte-1u5swoa" placeholder="Search by name or ID…"/> <!></div> <!> <div class="taclet-pane svelte-1u5swoa"><button class="taclet-header svelte-1u5swoa"><span class="taclet-toggle svelte-1u5swoa"> </span> <span class="taclet-title svelte-1u5swoa">Node Info</span> <!></button> <!></div></div> <!>',1);function Ns(t,e){fe(e,!0);let n=De(e,"appState",7);function r(A){const M=Y(A.name);return M==="open"?"open":M==="closed"?"closed":"inner"}function a(A){const M=A.name.length>20?A.name.slice(0,18)+"…":A.name;return`#${A.id.nodeId} ${M}`}const s=32,i=25,h=300;let d=X(je([])),l=X(""),u=X(!1),k=X(0),m=X(500),_=X(null),g=X(je({open:!1,x:0,y:0,node:null,pruning:!1,pruneError:null})),P=X(null),f=X(!0),y=null,F=!1,D=null;function L(A){F||(y!==null&&(clearTimeout(y),y=null),y=setTimeout(()=>{O(P,A,!0),y=null},180))}function N(){y!==null&&(clearTimeout(y),y=null)}const G=de(()=>{const A=o(l).trim().toLowerCase();if(A)return o(d).map((J,ye)=>({n:J,i:ye})).filter(({n:J})=>J.kind==="virtual"?!1:J.node.name.toLowerCase().includes(A)||J.node.id.nodeId.toString().includes(A));const M=Math.max(0,Math.floor(o(k)/s)-i),ie=Math.min(o(d).length,Math.ceil((o(k)+o(m))/s)+i);return o(d).slice(M,ie).map((J,ye)=>({n:J,i:M+ye}))}),U=de(()=>o(d).length*s),V=de(()=>o(l).trim()?0:Math.max(0,Math.floor(o(k)/s)-i)*s);function Y(A){const M=A.toUpperCase();return M.includes("OPEN")?"open":M.includes("CLOSED")?"closed":"unknown"}function x(A){const M=Y(A.name);return M==="open"||M==="closed"}function R(A){var M;return String((M=n().active_node)==null?void 0:M.nodeId)===String(A.id.nodeId)}function C(A,M,ie,J=!1){return{kind:"real",node:A,depth:M,logicalDepth:ie,expanded:!1,loading:!1,hasChildren:null,isChainNode:J}}async function S(A,M,ie,J,ye,be){if(be<=0)return[];const pe=await A.proofTreeChildren(M,ie.id);if(pe.length===0)return[];if(pe.length===1){const _e=pe[0],qe=C(_e,J,ye+1,!0),Ne=await S(A,M,_e,J,ye+1,be-1);return Ne.length>0&&(qe.expanded=!0),[qe,...Ne]}const Te=[];for(let _e=0;_e<pe.length;_e++)Te.push({kind:"virtual",label:`Branch ${_e+1}`,depth:J+1,logicalDepth:ye+1}),Te.push(C(pe[_e],J+2,ye+2));return Te}async function w(A){const M=o(d)[A];if(!(M.kind!=="real"||M.loading||n().proof==null)){M.loading=!0;try{const ie=await S(n().client,n().proof,M.node,M.depth,M.logicalDepth,h),J=o(d)[A];if((J==null?void 0:J.kind)!=="real"||J.node.id.nodeId!==M.node.id.nodeId)return;J.hasChildren=ie.length>0,ie.length>0?(J.expanded=!0,o(d).splice(A+1,0,...ie)):J.expanded=!1}catch(ie){console.error("Failed to expand node:",ie)}finally{M.loading=!1}}}function E(A){const M=o(d)[A];if(M.kind!=="real")return;M.expanded=!1;const ie=M.logicalDepth;let J=A+1;for(;J<o(d).length&&o(d)[J].logicalDepth>ie;)J++;o(d).splice(A+1,J-A-1)}function q(A){const M=o(d)[A];M.kind==="real"&&(M.expanded?E(A):w(A))}function j(A,M){A.preventDefault(),O(g,{open:!0,x:A.clientX,y:A.clientY,node:M,pruning:!1,pruneError:null},!0)}async function oe(){if(o(g).node){o(g).pruning=!0,o(g).pruneError=null;try{await n().client.proofPruneTo(o(g).node.id),o(g).open=!1,n().proofTreeChanged.notify()}catch(A){o(g).pruneError=A.toString(),o(g).pruning=!1}}}async function K(A,M){O(u,!0),O(d,[],!0);try{const ie=await A.proofTreeRoot(M),J=C(ie,0,0);O(d,[J],!0),await w(0)}finally{O(u,!1)}}function re(){for(const A of o(d))if(A.kind==="real"&&Y(A.node.name)==="open")return A.node.id;return null}ke(()=>{if(n().proofTreeChanged.count,n().proof==null){O(d,[],!0);return}K(n().client,n().proof).then(()=>{const A=re();A&&(n().active_node=A,n().active_node_status="open")})}),ke(()=>{if(!o(_))return;const A=new ResizeObserver(M=>{O(m,M[0].contentRect.height,!0)});return A.observe(o(_)),()=>A.disconnect()});function ue(A){O(k,A.target.scrollTop,!0),F=!0,y!==null&&(clearTimeout(y),y=null),D!==null&&clearTimeout(D),D=setTimeout(()=>{F=!1,D=null},120)}ke(()=>{if(!o(_)||!n().active_node)return;const A=o(d).findIndex(J=>{var ye;return J.kind==="real"&&String(J.node.id.nodeId)===String((ye=n().active_node)==null?void 0:ye.nodeId)});if(A===-1)return;const M=A*s,ie=M+s;Ht(()=>{if(!o(_))return;const J=o(m);(M<o(_).scrollTop||ie>o(_).scrollTop+J)&&(o(_).scrollTop=M-J/2+s/2)})});var we=Ls(),Z=ne(we),$=v(Z),ee=b(v($),2),I=v(ee);c(ee),c($);var Q=b($,2),te=v(Q);xe(te);var le=b(te,2);{var ce=A=>{var M=hs();z("click",M,()=>O(l,"")),p(A,M)};H(le,A=>{o(l)&&A(ce)})}c(Q);var se=b(Q,2);{var Ue=A=>{var M=ps();p(A,M)},He=A=>{var M=Es(),ie=v(M);{var J=pe=>{var Te=ys(),_e=v(Te);{var qe=ae=>{var Pe=ms();p(ae,Pe)},Ne=ae=>{var Pe=Se(),Oe=ne(Pe);me(Oe,17,()=>o(G),Ke,(wt,Bt)=>{let Le=()=>o(Bt).n;var Ve=Se(),at=ne(Ve);{var st=Je=>{var Re=gs();let vt;var Nt=v(Re),Ye=b(Nt,2),ht=v(Ye),Rt=v(ht,!0);c(ht);var Mt=b(ht);c(Ye),c(Re),B((it,Kt)=>{vt=Ie(Re,1,"node-row svelte-1u5swoa",null,vt,it),Ie(Nt,1,`status-dot status-${Kt??""}`,"svelte-1u5swoa"),W(Rt,Le().node.id.nodeId),W(Mt,` ${Le().node.name??""}`)},[()=>({active:R(Le().node),open:Y(Le().node.name)==="open",closed:Y(Le().node.name)==="closed"}),()=>Y(Le().node.name)]),z("click",Re,()=>{n().active_node=Le().node.id,n().active_node_status=r(Le().node)}),z("contextmenu",Re,it=>j(it,Le().node)),ze("mouseenter",Re,()=>L(Le().node)),ze("mouseleave",Re,N),p(Je,Re)};H(at,Je=>{Le().kind==="real"&&Je(st)})}p(wt,Ve)}),p(ae,Pe)};H(_e,ae=>{o(G).length===0?ae(qe):ae(Ne,-1)})}c(Te),p(pe,Te)},ye=de(()=>o(l).trim()),be=pe=>{var Te=Ts(),_e=v(Te);me(_e,21,()=>o(G),({n:qe,i:Ne})=>qe.kind==="real"?qe.node.id.nodeId:`v-${Ne}`,(qe,Ne)=>{let ae=()=>o(Ne).n,Pe=()=>o(Ne).i;var Oe=xs();et(Oe,"height: 32px;");var wt=v(Oe);{var Bt=Ve=>{var at=ks(),st=ne(at),Je=b(st,2);{var Re=We=>{var Xe=bs();p(We,Xe)},vt=de(()=>ae().isChainNode||x(ae().node)),Nt=We=>{var Xe=_s(),Vt=v(Xe);{var vo=Me=>{var lt=ws();p(Me,lt)},ho=Me=>{var lt=yt("▾");p(Me,lt)},po=Me=>{var lt=yt(" ");p(Me,lt)},mo=Me=>{var lt=yt("▸");p(Me,lt)};H(Vt,Me=>{ae().loading?Me(vo):ae().expanded?Me(ho,1):ae().hasChildren===!1?Me(po,2):Me(mo,-1)})}c(Xe),B(()=>Fe(Xe,"title",ae().expanded?"Collapse":"Expand")),z("click",Xe,()=>q(Pe())),p(We,Xe)};H(Je,We=>{o(vt)?We(Re):We(Nt,-1)})}var Ye=b(Je,2);let ht;var Rt=v(Ye),Mt=b(Rt,2),it=v(Mt),Kt=v(it,!0);c(it);var fo=b(it);c(Mt),c(Ye),B((We,Xe,Vt)=>{et(st,`width: ${We??""}px; flex-shrink: 0;`),ht=Ie(Ye,1,"node-row svelte-1u5swoa",null,ht,Xe),Ie(Rt,1,`status-dot status-${Vt??""}`,"svelte-1u5swoa"),W(Kt,ae().node.id.nodeId),W(fo,` ${ae().node.name??""}`)},[()=>Math.min(ae().depth*12,180)+8,()=>({active:R(ae().node),open:Y(ae().node.name)==="open",closed:Y(ae().node.name)==="closed"}),()=>Y(ae().node.name)]),z("click",Ye,()=>{n().active_node=ae().node.id,n().active_node_status=r(ae().node)}),z("contextmenu",Ye,We=>j(We,ae().node)),ze("mouseenter",Ye,()=>L(ae().node)),ze("mouseleave",Ye,N),p(Ve,at)},Le=Ve=>{var at=Ss(),st=ne(at),Je=b(st,2),Re=b(v(Je));c(Je),B(vt=>{et(st,`width: ${vt??""}px; flex-shrink: 0;`),W(Re,` ${ae().label??""}`)},[()=>Math.min(ae().depth*12,180)+8]),p(Ve,at)};H(wt,Ve=>{ae().kind==="real"?Ve(Bt):Ve(Le,-1)})}c(Oe),p(qe,Oe)}),c(_e),c(Te),B(()=>{et(Te,`height: ${o(U)??""}px;`),et(_e,`transform: translateY(${o(V)??""}px);`)}),p(pe,Te)};H(ie,pe=>{o(ye)?pe(J):pe(be,-1)})}c(M),nt(M,pe=>O(_,pe),()=>o(_)),ze("scroll",M,ue),p(A,M)};H(se,A=>{o(u)?A(Ue):A(He,-1)})}var ft=b(se,2),rt=v(ft),Ce=v(rt),Lt=v(Ce,!0);c(Ce);var so=b(Ce,4);{var io=A=>{var M=Is(),ie=v(M,!0);c(M),B(J=>W(ie,J),[()=>o(P).name.length>24?o(P).name.slice(0,22)+"…":o(P).name]),p(A,M)};H(so,A=>{o(P)&&!o(f)&&A(io)})}c(rt);var lo=b(rt,2);{var co=A=>{var M=Cs(),ie=v(M);{var J=be=>{us(be,{get appState(){return n()},get nodeId(){return o(P).id},get nodeName(){return o(P).name}})},ye=be=>{var pe=As();p(be,pe)};H(ie,be=>{o(P)?be(J):be(ye,-1)})}c(M),p(A,M)};H(lo,A=>{o(f)&&A(co)})}c(ft),c(Z);var uo=b(Z,2);no(uo,{get open(){return o(g).open},get positionX(){return o(g).x},get positionY(){return o(g).y},onClose:()=>o(g).open=!1,children:(A,M)=>{var ie=Os(),J=v(ie),ye=v(J);c(J);var be=b(J,4),pe=b(v(be),2),Te=v(pe,!0);c(pe),c(be);var _e=b(be,2);{var qe=Pe=>{var Oe=Ps(),wt=v(Oe,!0);c(Oe),B(()=>W(wt,o(g).pruneError)),p(Pe,Oe)};H(_e,Pe=>{o(g).pruneError&&Pe(qe)})}var Ne=b(_e,4),ae=b(Ne,2);c(ie),B(()=>{var Pe,Oe;W(ye,`#${((Pe=o(g).node)==null?void 0:Pe.id.nodeId)??""} — ${((Oe=o(g).node)==null?void 0:Oe.name)??""??""}`),be.disabled=o(g).pruning,W(Te,o(g).pruning?"Pruning…":"Prune to Here")}),z("click",be,oe),z("click",Ne,()=>{$e.openInTab(o(g).node.id,a(o(g).node),r(o(g).node)),o(g).open=!1}),z("click",ae,()=>{$e.openInSplit(o(g).node.id,a(o(g).node),r(o(g).node)),o(g).open=!1}),p(A,ie)},$$slots:{default:!0}}),B(()=>{W(I,`${o(d).length??""} nodes`),Fe(rt,"title",o(f)?"Collapse node info":"Expand node info"),W(Lt,o(f)?"▾":"▸")}),tt(te,()=>o(l),A=>O(l,A)),z("click",rt,()=>O(f,!o(f))),p(t,we),ve()}ge(["click","contextmenu"]);const Rs={id:"tree",label:"Proof Tree",order:10,defaultFlex:2,minWidth:120,component:Ns},Ms=Object.freeze(Object.defineProperty({__proto__:null,pane:Rs},Symbol.toStringTag,{value:"Module"}));async function oo(t){if(Ae){const{writeText:e}=await lr(async()=>{const{writeText:n}=await import("./6pjeCr8X.js");return{writeText:n}},[],import.meta.url);await e(t)}else await navigator.clipboard.writeText(t)}var Ds=T('<span role="button" tabindex="0"> </span>'),js=T('<button class="menu-item svelte-r00w4i"><span>Copy term</span> <span class="menu-hint svelte-r00w4i">⧉</span></button>'),Fs=T('<div class="menu-sep svelte-r00w4i" role="separator"></div>'),qs=T('<div class="menu-header svelte-r00w4i"> </div>'),Gs=T("<button> </button>"),zs=T('<button class="menu-item svelte-r00w4i"> </button>'),Us=T('<div class="menu-submenu-host svelte-r00w4i"><div class="menu-item menu-has-sub svelte-r00w4i"><span> </span> <span class="menu-arrow svelte-r00w4i">▶</span></div> <div class="menu-submenu svelte-r00w4i"></div></div>'),Hs=T('<div class="tree svelte-r00w4i"><!> <!></div>');function Ys(t,e){fe(e,!0);let n=De(e,"nodeStatus",3,null),r=De(e,"searchMatches",19,()=>[]),a=De(e,"currentMatchIdx",3,0);function s(x,R,C,S){if(!R||R.length===0)return[{content:x,spans:[C],textStart:S}];const w=[...R].sort((K,re)=>K.start-re.start);let E=[],q=[],j=0;for(const K of w){j!==K.start&&(q.push(E.length),E.push({content:x.slice(j,K.start),spans:[],textStart:S+j}));const re=x.slice(K.start,K.end);if(re.length!==0){const ue=s(re,K.children||[],C+E.length,S+K.start);E=E.concat(ue)}j=K.end}j<x.length&&(q.push(E.length),E.push({content:x.slice(j),spans:[],textStart:S+j}));const oe=C+E.length;for(const K of q)for(let re=C;re<oe;re++)E[K].spans.push(re);return E}const i=de(()=>s(e.sequent.sequent,e.sequent.terms,0,0));let h=X(null);function d(x){return o(h)===null?!1:o(i)[o(h)].spans.includes(x)}function l(x,R,C){return R<x.textStart+x.content.length&&C>x.textStart}function u(x){return r().some(R=>l(o(i)[x],R.start,R.end))}function k(x){if(r().length===0||a()>=r().length)return!1;const R=r()[a()];return l(o(i)[x],R.start,R.end)}let m=X(null);ke(()=>{if(a(),r(),!o(m))return;const x=o(m).querySelector(".span-match-current");x==null||x.scrollIntoView({block:"nearest",behavior:"smooth"})});const _=8,g=25;function P(x){return x.displayName?x.displayName:(x.commandId.id.split(":")[1]??x.commandId.id).split(" ")[0]}function f(x){if(x.length===0)return[];const R=x.map(w=>({kind:"item",label:P(w),action:w.commandId}));if(R.length<=_)return R;const C=R.slice(0,_),S=R.slice(_);for(let w=0;w<S.length;w+=g){const E=S.slice(w,w+g),q=w/g;C.push({kind:"sub",label:q===0?"More rules":`More rules (${q+1})`,children:E})}return C}let y=X(je({open:!1,x:0,y:0,clickedIndex:-1,actions:{taclets:[],macros:[],other:[]}}));function F(){const x=o(y).clickedIndex;return x<0||x>=o(i).length?"":[...o(i)[x].spans.length>0?o(i)[x].spans:[x]].sort((C,S)=>C-S).map(C=>o(i)[C].content).join("")}async function D(){const x=F();o(y).open=!1,x&&await oo(x)}const L=de(()=>{const{taclets:x,macros:R,other:C}=o(y).actions;if(x.length+R.length+C.length===0)return[{kind:"item",label:"No rules applicable",action:null},{kind:"sep"},{kind:"copy"}];const w=[];function E(q,j){j.length!==0&&(w.length>0&&w.push({kind:"sep"}),w.push({kind:"header",label:q}),w.push(...f(j)))}return E("Taclets",x),E("Macros",R),E("Other",C),w.push({kind:"sep"}),w.push({kind:"copy"}),w});function N(x,R){if(n()==="closed"){O(y,{open:!0,x:x.pageX,y:x.pageY,clickedIndex:R,actions:{taclets:[],macros:[],other:[]}},!0);return}const C=o(i)[R].textStart;e.appState.client.goalActions(e.sequent.id,C).then(S=>{const w=n()==="inner";O(y,{open:!0,x:x.pageX,y:x.pageY,clickedIndex:R,actions:{taclets:w?[]:S.filter(E=>E.kind===xt.Taclet),macros:S.filter(E=>E.kind===xt.Macro),other:w?[]:S.filter(E=>E.kind!==xt.Taclet&&E.kind!==xt.Macro)}},!0)})}function G(x){x&&(o(y).open=!1,e.appState.client.applyAction(x).then(R=>{R?e.appState.proofTreeChanged.notify():console.error("failed to apply rule")}).catch(R=>{}))}var U=Hs(),V=v(U);me(V,17,()=>o(i),Ke,(x,R,C)=>{var S=Ds();let w;var E=v(S,!0);c(S),B(q=>{w=Ie(S,1,"piece svelte-r00w4i",null,w,q),W(E,o(R).content)},[()=>({"span-hover":d(C),"span-match":u(C),"span-match-current":k(C),"no-action":n()==="closed"})]),z("mouseover",S,()=>O(h,C,!0)),ze("focus",S,()=>O(h,C,!0)),z("mouseout",S,()=>{o(h)===C&&O(h,null)}),ze("blur",S,()=>{o(h)===C&&O(h,null)}),z("click",S,q=>N(q,C)),p(x,S)});var Y=b(V,2);no(Y,{get open(){return o(y).open},onClose:()=>o(y).open=!1,get positionX(){return o(y).x},get positionY(){return o(y).y},children:(x,R)=>{var C=Se(),S=ne(C);me(S,17,()=>o(L),Ke,(w,E)=>{var q=Se(),j=ne(q);{var oe=Z=>{var $=js();z("click",$,D),p(Z,$)},K=Z=>{var $=Fs();p(Z,$)},re=Z=>{var $=qs(),ee=v($,!0);c($),B(()=>W(ee,o(E).label)),p(Z,$)},ue=Z=>{var $=Gs();let ee;var I=v($,!0);c($),B(()=>{ee=Ie($,1,"menu-item svelte-r00w4i",null,ee,{"menu-empty":!o(E).action}),$.disabled=!o(E).action,W(I,o(E).label)}),z("click",$,()=>G(o(E).action)),p(Z,$)},we=Z=>{var $=Us(),ee=v($),I=v(ee),Q=v(I,!0);c(I),fn(2),c(ee);var te=b(ee,2);me(te,21,()=>o(E).children,Ke,(le,ce)=>{var se=zs(),Ue=v(se,!0);c(se),B(()=>W(Ue,o(ce).label)),z("click",se,()=>G(o(ce).action)),p(le,se)}),c(te),c($),B(()=>W(Q,o(E).label)),p(Z,$)};H(j,Z=>{o(E).kind==="copy"?Z(oe):o(E).kind==="sep"?Z(K,1):o(E).kind==="header"?Z(re,2):o(E).kind==="item"?Z(ue,3):o(E).kind==="sub"&&Z(we,4)})}p(w,q)}),p(x,C)},$$slots:{default:!0}}),c(U),nt(U,x=>O(m,x),()=>o(m)),p(t,U),ve()}ge(["mouseover","mouseout","click"]);var Ws=Mn('<svg class="copy-icon svelte-yo0rx" viewBox="0 0 16 16" fill="none" stroke="currentColor" stroke-width="1.4"><rect x="5.5" y="5.5" width="8" height="8" rx="1.5"></rect><path d="M10.5 5.5V4A1.5 1.5 0 0 0 9 2.5H4A1.5 1.5 0 0 0 2.5 4v5A1.5 1.5 0 0 0 4 10.5h1.5"></path></svg>'),Bs=T('<button class="search-open-btn svelte-yo0rx">⌕</button>'),Ks=T('<div class="search-bar svelte-yo0rx"><input type="text" class="search-input svelte-yo0rx" placeholder="Find in sequent…"/> <span class="match-count svelte-yo0rx"><!></span> <button class="search-nav-btn svelte-yo0rx">‹</button> <button class="search-nav-btn svelte-yo0rx" title="Next match (Enter)">›</button> <button class="search-close-btn svelte-yo0rx" title="Close (Escape)">✕</button></div>'),Vs=T("<span></span>"),Js=T('<div class="sequent-container svelte-yo0rx"><div class="sequent-header svelte-yo0rx"><h3 class="svelte-yo0rx">Sequent</h3> <div class="header-btns svelte-yo0rx"><button class="search-open-btn svelte-yo0rx" title="Copy sequent to clipboard"><!></button> <!></div></div> <!> <div class="sequent-content svelte-yo0rx"><code class="character-width-estimator svelte-yo0rx">x</code> <pre class="svelte-yo0rx"><code class="svelte-yo0rx"><!></code></pre></div></div>');function Xs(t,e){fe(e,!0);let n=De(e,"pinnedNodeId",3,null),r=De(e,"nodeStatus",3,null);const a=de(()=>n()??e.appState.active_node);let s=X(null),i=X(120),h=X(null),d=X(null),l=X(!1),u=X(""),k=X(0),m=X(null);const _=de(()=>{var ce;const I=o(u).trim().toLowerCase();if(!I||!((ce=o(s))!=null&&ce.sequent))return[];const Q=o(s).sequent.toLowerCase(),te=[];let le=0;for(;;){const se=Q.indexOf(I,le);if(se===-1)break;te.push({start:se,end:se+I.length}),le=se+1}return te});ke(()=>{o(_),O(k,0)});function g(){o(_).length!==0&&O(k,(o(k)+1)%o(_).length)}function P(){o(_).length!==0&&O(k,(o(k)-1+o(_).length)%o(_).length)}function f(){O(l,!0),setTimeout(()=>{var I;return(I=o(m))==null?void 0:I.focus()},0)}function y(){O(l,!1),O(u,"")}function F(I){I.key==="Escape"?y():I.key==="Enter"&&(I.shiftKey?P():g(),I.preventDefault())}function D(I){(I.metaKey||I.ctrlKey)&&I.key==="f"&&(f(),I.preventDefault())}let L=X(!1),N=null;async function G(){var Q;const I=(Q=o(s))==null?void 0:Q.sequent;I&&(await oo(I),O(L,!0),N!==null&&clearTimeout(N),N=setTimeout(()=>{O(L,!1),N=null},1200))}async function U(I,Q,te){const le={unicode:!1,width:te,indentation:0,pure:!1,termLabels:!0};return I.goalPrint(Q,le)}ke(()=>{if(!o(h)||!o(d))return;const I=new ResizeObserver(Q=>{const te=Q[0].contentRect.width,le=o(d).offsetWidth,ce=Math.floor(te/le);O(i,ce,!0)});return I.observe(o(h)),()=>I.disconnect()}),ke(()=>{e.appState.proof==null||o(a)==null||U(e.appState.client,o(a),o(i)).then(I=>{O(s,I,!0)}).catch(I=>{console.error("fetchSequent failed:",I)})});var V=Js();ze("keydown",Yt,D);var Y=v(V),x=b(v(Y),2),R=v(x),C=v(R);{var S=I=>{var Q=yt("✓");p(I,Q)},w=I=>{var Q=Ws();p(I,Q)};H(C,I=>{o(L)?I(S):I(w,-1)})}c(R);var E=b(R,2);{var q=I=>{var Q=Bs();B(te=>Fe(Q,"title",`Search (${te??""})`),[()=>Gt("mod+F")]),z("click",Q,f),p(I,Q)};H(E,I=>{o(l)||I(q)})}c(x),c(Y);var j=b(Y,2);{var oe=I=>{var Q=Ks(),te=v(Q);xe(te),nt(te,Ce=>O(m,Ce),()=>o(m));var le=b(te,2),ce=v(le);{var se=Ce=>{var Lt=yt();B(()=>W(Lt,o(_).length===0?"No matches":`${o(k)+1} / ${o(_).length}`)),p(Ce,Lt)},Ue=de(()=>o(u).trim());H(ce,Ce=>{o(Ue)&&Ce(se)})}c(le);var He=b(le,2),ft=b(He,2),rt=b(ft,2);c(Q),B(Ce=>{He.disabled=o(_).length===0,Fe(He,"title",`Previous match (${Ce??""})`),ft.disabled=o(_).length===0},[()=>Gt("shift+Enter")]),z("keydown",te,F),tt(te,()=>o(u),Ce=>O(u,Ce)),z("click",He,P),z("click",ft,g),z("click",rt,y),p(I,Q)};H(j,I=>{o(l)&&I(oe)})}var K=b(j,2),re=v(K);nt(re,I=>O(d,I),()=>o(d));var ue=b(re,2),we=v(ue),Z=v(we);{var $=I=>{var Q=Se(),te=ne(Q);Jn(te,()=>o(s),le=>{Ys(le,{get appState(){return e.appState},get sequent(){return o(s)},get nodeStatus(){return r()},get searchMatches(){return o(_)},get currentMatchIdx(){return o(k)}})}),p(I,Q)},ee=I=>{var Q=Vs();Q.textContent="<no sequent loaded>",p(I,Q)};H(Z,I=>{var Q,te;(Q=o(s))!=null&&Q.sequent&&((te=o(s))!=null&&te.terms)?I($):I(ee,-1)})}c(we),c(ue),c(K),nt(K,I=>O(h,I),()=>o(h)),c(V),B(()=>{var I;return R.disabled=!((I=o(s))!=null&&I.sequent)}),z("click",R,G),p(t,V),ve()}ge(["click","keydown"]);var Qs=T('<span class="tab-x svelte-1f726zb" aria-label="Close tab">×</span>'),Zs=T('<button><span class="tab-label svelte-1f726zb"> </span> <!></button>'),$s=T('<button class="col-close-btn svelte-1f726zb" title="Close this split" aria-label="Close split pane">✕</button>'),ei=T('<div class="sequent-pane svelte-1f726zb"><div class="tab-bar svelte-1f726zb"><!> <!></div> <div class="tab-content svelte-1f726zb"><!></div></div>');function ti(t,e){fe(e,!0);let n=De(e,"style",3,"");const r=de(()=>e.column.tabs.find(m=>m.id===e.column.activeTabId)??e.column.tabs[0]),a=de(()=>e.column.tabs.length>1||e.showClose);var s=ei(),i=v(s),h=v(i);me(h,17,()=>e.column.tabs,m=>m.id,(m,_)=>{var g=Zs();let P;var f=v(g),y=v(f,!0);c(f);var F=b(f,2);{var D=L=>{var N=Qs();z("click",N,G=>{G.stopPropagation(),e.onTabClose(o(_).id)}),p(L,N)};H(F,L=>{o(a)&&L(D)})}c(g),B(()=>{P=Ie(g,1,"tab svelte-1f726zb",null,P,{active:o(_).id===e.column.activeTabId,following:o(_).nodeId===null}),Fe(g,"title",o(_).nodeId===null?"Following active selection":`Node ${o(_).nodeId.nodeId}: ${o(_).label}`),W(y,o(_).label)}),z("click",g,()=>e.onActivate(o(_).id)),p(m,g)});var d=b(h,2);{var l=m=>{var _=$s();z("click",_,function(...g){var P;(P=e.onColumnClose)==null||P.apply(this,g)}),p(m,_)};H(d,m=>{e.showClose&&m(l)})}c(i);var u=b(i,2),k=v(u);Zn(k,{children:(m,_)=>{var g=Se(),P=ne(g);{var f=y=>{var F=Se(),D=ne(F);Jn(D,()=>o(r).id,L=>{{let N=de(()=>o(r).nodeId?o(r).nodeStatus??null:e.appState.active_node_status);Xs(L,{get appState(){return e.appState},get pinnedNodeId(){return o(r).nodeId},get nodeStatus(){return o(N)}})}}),p(y,F)};H(P,y=>{o(r)&&y(f)})}p(m,g)}}),c(u),c(s),B(()=>et(s,n())),p(t,s),ve()}ge(["click"]);var ni=T('<div aria-hidden="true"></div>');function ro(t,e){fe(e,!0);let n=X(!1);function r(i){if(i.button!==0)return;i.preventDefault(),O(n,!0);let h=i.clientX;function d(u){const k=u.clientX-h;k!==0&&(h=u.clientX,e.onDrag(k))}function l(){O(n,!1),window.removeEventListener("mousemove",d),window.removeEventListener("mouseup",l)}window.addEventListener("mousemove",d),window.addEventListener("mouseup",l)}var a=ni();let s;B(()=>s=Ie(a,1,"resize-handle svelte-98yjt2",null,s,{dragging:o(n)})),z("mousedown",a,r),p(t,a),ve()}ge(["mousedown"]);var oi=T("<!> <!>",1),ri=T('<div class="sequent-area svelte-xlyzcm"></div>');function ai(t,e){fe(e,!0);let n=X(null);var r=ri();me(r,23,()=>$e.columns,a=>a.id,(a,s,i)=>{var h=oi(),d=ne(h);{var l=k=>{ro(k,{onDrag:m=>{var _;return $e.resizeColumns(o(i)-1,m,((_=o(n))==null?void 0:_.clientWidth)??0)}})};H(d,k=>{o(i)>0&&k(l)})}var u=b(d,2);{let k=de(()=>$e.columns.length>1);ti(u,{get column(){return o(s)},get appState(){return e.appState},get showClose(){return o(k)},onTabClose:m=>$e.closeTab(o(s).id,m),onColumnClose:()=>$e.closeColumn(o(s).id),onActivate:m=>$e.setActiveTab(o(s).id,m),get style(){return`flex: ${o(s).flex??""} 1 0; min-width: 150px;`}})}p(a,h)}),c(r),nt(r,a=>O(n,a),()=>o(n)),p(t,r),ve()}const si={id:"sequent",label:"Sequent",order:20,defaultFlex:7,minWidth:200,chrome:"bare",component:ai},ii=Object.freeze(Object.defineProperty({__proto__:null,pane:si},Symbol.toStringTag,{value:"Module"})),li=Object.assign({"./defs/goals.ts":as,"./defs/proof-tree.ts":Ms,"./defs/sequent-area.ts":ii}),dt=Object.values(li).map(t=>t.pane).filter(t=>t!=null).sort((t,e)=>t.order-e.order);var Ln=T("<option> </option>"),ci=T('<span class="using-global svelte-c7qdii">using global</span>'),di=T('<div><label class="check-row svelte-c7qdii"><input type="checkbox" class="svelte-c7qdii"/> <span class="pane-name svelte-c7qdii"> </span> <!></label> <div><div class="field wide"><select class="input"></select></div> <div class="field narrow"><input type="number" class="input" min="8" max="32" step="1"/></div></div></div>'),ui=T('<h3 class="section-label">Global Font</h3> <p class="hint">Applies to all panes unless a pane has its own override.</p> <div class="row"><div class="field wide"><label for="gf-fam">Family</label> <select id="gf-fam" class="input"></select></div> <div class="field narrow"><label for="gf-sz">Size (px)</label> <input id="gf-sz" type="number" class="input" min="8" max="32" step="1"/></div></div> <h3 class="section-label" style="margin-top: 20px;">Per-pane Overrides</h3> <p class="hint">Enable a pane to use a different font from the global setting.</p> <div class="pane-list svelte-c7qdii"></div>',1);function fi(t,e){fe(e,!0);let n=De(e,"draft",7);var r=ui(),a=b(ne(r),4),s=v(a),i=b(v(s),2);me(i,21,()=>Pn,Ke,(u,k)=>{var m=Ln(),_=v(m,!0);c(m);var g={};B(()=>{W(_,o(k).label),g!==(g=o(k).value)&&(m.value=(m.__value=o(k).value)??"")}),p(u,m)}),c(i),c(s);var h=b(s,2),d=b(v(h),2);xe(d),c(h),c(a);var l=b(a,6);me(l,21,()=>dt,Ke,(u,k)=>{let m=()=>o(k).id,_=()=>o(k).label;const g=de(()=>n().fonts.panes[m()]);var P=di();let f;var y=v(P),F=v(y);xe(F);var D=b(F,2),L=v(D,!0);c(D);var N=b(D,2);{var G=S=>{var w=ci();p(S,w)};H(N,S=>{o(g).useOverride||S(G)})}c(y);var U=b(y,2);let V;var Y=v(U),x=v(Y);me(x,21,()=>Pn,Ke,(S,w)=>{var E=Ln(),q=v(E,!0);c(E);var j={};B(()=>{W(q,o(w).label),j!==(j=o(w).value)&&(E.value=(E.__value=o(w).value)??"")}),p(S,E)}),c(x),c(Y);var R=b(Y,2),C=v(R);xe(C),c(R),c(U),c(P),B(()=>{f=Ie(P,1,"pane-card svelte-c7qdii",null,f,{on:o(g).useOverride}),W(L,_()),V=Ie(U,1,"row svelte-c7qdii",null,V,{dim:!o(g).useOverride}),x.disabled=!o(g).useOverride,C.disabled=!o(g).useOverride}),xr(F,()=>o(g).useOverride,S=>o(g).useOverride=S),xn(x,()=>o(g).font.family,S=>o(g).font.family=S),tt(C,()=>o(g).font.size,S=>o(g).font.size=S),p(u,P)}),c(l),xn(i,()=>n().fonts.global.family,u=>n().fonts.global.family=u),tt(d,()=>n().fonts.global.size,u=>n().fonts.global.size=u),p(t,r),ve()}const vi={id:"fonts",label:"Fonts",icon:"Aa",order:30,component:fi,createDraft:t=>{var n,r;const e=structuredClone(t.fonts);for(const a of dt)(n=e.panes)[r=a.id]??(n[r]=structuredClone(Ta));return{fonts:e}},applyDraft:(t,e)=>({...e,fonts:t.fonts})},hi=Object.freeze(Object.defineProperty({__proto__:null,section:vi},Symbol.toStringTag,{value:"Module"})),pi=Object.assign({"./defs/backend.ts":qa,"./defs/connection.ts":Xa,"./defs/fonts.ts":hi}),ct=Object.values(pi).map(t=>t.section).filter(t=>t!=null).sort((t,e)=>t.order-e.order);var mi=T('<button><span class="icon svelte-e3b7dy"> </span> </button>'),gi=T('<div class="pref svelte-e3b7dy"><h2 class="pref-title svelte-e3b7dy">Preferences</h2> <div class="pref-body svelte-e3b7dy"><nav class="sidebar svelte-e3b7dy"></nav> <div class="content svelte-e3b7dy"><!></div></div> <div class="actions svelte-e3b7dy"><button class="btn-cancel svelte-e3b7dy">Cancel</button> <button class="btn-save svelte-e3b7dy">Save</button></div></div>');function yi(t,e){fe(e,!0);const n=()=>Vn(bt,"$preferences",r),[r,a]=Kn();let s=X(je({})),i=X(je(ct[0].id));const h=de(()=>ct.find(l=>l.id===o(i))??ct[0]);ke(()=>{if(e.open){const l=n(),u={};for(const k of ct)u[k.id]=k.createDraft(l);O(s,u,!0),O(i,ct[0].id,!0)}});function d(){var g;const l=n().connection;let u=n();for(const P of ct)u=P.applyDraft(o(s)[P.id],u);const k=n().jarPaths??{};bt.set(u);const m=JSON.stringify(l)!==JSON.stringify(u.connection),_=(k[u.flavor]??"")!==(((g=u.jarPaths)==null?void 0:g[u.flavor])??"");(m||_)&&e.onApply(u.connection),e.onClose()}zt(t,{get open(){return e.open},get onclose(){return e.onClose},closeOnBackdrop:!1,children:(l,u)=>{var k=gi(),m=b(v(k),2),_=v(m);me(_,21,()=>ct,Ke,(L,N)=>{var G=mi();let U;var V=v(G),Y=v(V,!0);c(V);var x=b(V);c(G),B(()=>{U=Ie(G,1,"tab svelte-e3b7dy",null,U,{active:o(i)===o(N).id}),W(Y,o(N).icon),W(x,` ${o(N).label??""}`)}),z("click",G,()=>O(i,o(N).id,!0)),p(L,G)}),c(_);var g=b(_,2),P=v(g);{var f=L=>{const N=de(()=>o(h).component);var G=Se(),U=ne(G);qt(U,()=>o(N),(V,Y)=>{Y(V,{get draft(){return o(s)[o(i)]}})}),p(L,G)};H(P,L=>{o(s)[o(i)]&&L(f)})}c(g),c(m);var y=b(m,2),F=v(y),D=b(F,2);c(y),c(k),z("click",F,function(...L){var N;(N=e.onClose)==null||N.apply(this,L)}),z("click",D,d),p(l,k)},$$slots:{default:!0}}),ve(),a()}ge(["click"]);const bi="0.1.0",wi="GPL-3.0-or-later",Nn={version:bi,license:wi},_i=`                    GNU GENERAL PUBLIC LICENSE
                       Version 3, 29 June 2007

 Copyright (C) 2007 Free Software Foundation, Inc. <https://fsf.org/>
 Everyone is permitted to copy and distribute verbatim copies
 of this license document, but changing it is not allowed.

                            Preamble

  The GNU General Public License is a free, copyleft license for
software and other kinds of works.

  The licenses for most software and other practical works are designed
to take away your freedom to share and change the works.  By contrast,
the GNU General Public License is intended to guarantee your freedom to
share and change all versions of a program--to make sure it remains free
software for all its users.  We, the Free Software Foundation, use the
GNU General Public License for most of our software; it applies also to
any other work released this way by its authors.  You can apply it to
your programs, too.

  When we speak of free software, we are referring to freedom, not
price.  Our General Public Licenses are designed to make sure that you
have the freedom to distribute copies of free software (and charge for
them if you wish), that you receive source code or can get it if you
want it, that you can change the software or use pieces of it in new
free programs, and that you know you can do these things.

  To protect your rights, we need to prevent others from denying you
these rights or asking you to surrender the rights.  Therefore, you have
certain responsibilities if you distribute copies of the software, or if
you modify it: responsibilities to respect the freedom of others.

  For example, if you distribute copies of such a program, whether
gratis or for a fee, you must pass on to the recipients the same
freedoms that you received.  You must make sure that they, too, receive
or can get the source code.  And you must show them these terms so they
know their rights.

  Developers that use the GNU GPL protect your rights with two steps:
(1) assert copyright on the software, and (2) offer you this License
giving you legal permission to copy, distribute and/or modify it.

  For the developers' and authors' protection, the GPL clearly explains
that there is no warranty for this free software.  For both users' and
authors' sake, the GPL requires that modified versions be marked as
changed, so that their problems will not be attributed erroneously to
authors of previous versions.

  Some devices are designed to deny users access to install or run
modified versions of the software inside them, although the manufacturer
can do so.  This is fundamentally incompatible with the aim of
protecting users' freedom to change the software.  The systematic
pattern of such abuse occurs in the area of products for individuals to
use, which is precisely where it is most unacceptable.  Therefore, we
have designed this version of the GPL to prohibit the practice for those
products.  If such problems arise substantially in other domains, we
stand ready to extend this provision to those domains in future versions
of the GPL, as needed to protect the freedom of users.

  Finally, every program is threatened constantly by software patents.
States should not allow patents to restrict development and use of
software on general-purpose computers, but in those that do, we wish to
avoid the special danger that patents applied to a free program could
make it effectively proprietary.  To prevent this, the GPL assures that
patents cannot be used to render the program non-free.

  The precise terms and conditions for copying, distribution and
modification follow.

                       TERMS AND CONDITIONS

  0. Definitions.

  "This License" refers to version 3 of the GNU General Public License.

  "Copyright" also means copyright-like laws that apply to other kinds of
works, such as semiconductor masks.

  "The Program" refers to any copyrightable work licensed under this
License.  Each licensee is addressed as "you".  "Licensees" and
"recipients" may be individuals or organizations.

  To "modify" a work means to copy from or adapt all or part of the work
in a fashion requiring copyright permission, other than the making of an
exact copy.  The resulting work is called a "modified version" of the
earlier work or a work "based on" the earlier work.

  A "covered work" means either the unmodified Program or a work based
on the Program.

  To "propagate" a work means to do anything with it that, without
permission, would make you directly or secondarily liable for
infringement under applicable copyright law, except executing it on a
computer or modifying a private copy.  Propagation includes copying,
distribution (with or without modification), making available to the
public, and in some countries other activities as well.

  To "convey" a work means any kind of propagation that enables other
parties to make or receive copies.  Mere interaction with a user through
a computer network, with no transfer of a copy, is not conveying.

  An interactive user interface displays "Appropriate Legal Notices"
to the extent that it includes a convenient and prominently visible
feature that (1) displays an appropriate copyright notice, and (2)
tells the user that there is no warranty for the work (except to the
extent that warranties are provided), that licensees may convey the
work under this License, and how to view a copy of this License.  If
the interface presents a list of user commands or options, such as a
menu, a prominent item in the list meets this criterion.

  1. Source Code.

  The "source code" for a work means the preferred form of the work
for making modifications to it.  "Object code" means any non-source
form of a work.

  A "Standard Interface" means an interface that either is an official
standard defined by a recognized standards body, or, in the case of
interfaces specified for a particular programming language, one that
is widely used among developers working in that language.

  The "System Libraries" of an executable work include anything, other
than the work as a whole, that (a) is included in the normal form of
packaging a Major Component, but which is not part of that Major
Component, and (b) serves only to enable use of the work with that
Major Component, or to implement a Standard Interface for which an
implementation is available to the public in source code form.  A
"Major Component", in this context, means a major essential component
(kernel, window system, and so on) of the specific operating system
(if any) on which the executable work runs, or a compiler used to
produce the work, or an object code interpreter used to run it.

  The "Corresponding Source" for a work in object code form means all
the source code needed to generate, install, and (for an executable
work) run the object code and to modify the work, including scripts to
control those activities.  However, it does not include the work's
System Libraries, or general-purpose tools or generally available free
programs which are used unmodified in performing those activities but
which are not part of the work.  For example, Corresponding Source
includes interface definition files associated with source files for
the work, and the source code for shared libraries and dynamically
linked subprograms that the work is specifically designed to require,
such as by intimate data communication or control flow between those
subprograms and other parts of the work.

  The Corresponding Source need not include anything that users
can regenerate automatically from other parts of the Corresponding
Source.

  The Corresponding Source for a work in source code form is that
same work.

  2. Basic Permissions.

  All rights granted under this License are granted for the term of
copyright on the Program, and are irrevocable provided the stated
conditions are met.  This License explicitly affirms your unlimited
permission to run the unmodified Program.  The output from running a
covered work is covered by this License only if the output, given its
content, constitutes a covered work.  This License acknowledges your
rights of fair use or other equivalent, as provided by copyright law.

  You may make, run and propagate covered works that you do not
convey, without conditions so long as your license otherwise remains
in force.  You may convey covered works to others for the sole purpose
of having them make modifications exclusively for you, or provide you
with facilities for running those works, provided that you comply with
the terms of this License in conveying all material for which you do
not control copyright.  Those thus making or running the covered works
for you must do so exclusively on your behalf, under your direction
and control, on terms that prohibit them from making any copies of
your copyrighted material outside their relationship with you.

  Conveying under any other circumstances is permitted solely under
the conditions stated below.  Sublicensing is not allowed; section 10
makes it unnecessary.

  3. Protecting Users' Legal Rights From Anti-Circumvention Law.

  No covered work shall be deemed part of an effective technological
measure under any applicable law fulfilling obligations under article
11 of the WIPO copyright treaty adopted on 20 December 1996, or
similar laws prohibiting or restricting circumvention of such
measures.

  When you convey a covered work, you waive any legal power to forbid
circumvention of technological measures to the extent such circumvention
is effected by exercising rights under this License with respect to
the covered work, and you disclaim any intention to limit operation or
modification of the work as a means of enforcing, against the work's
users, your or third parties' legal rights to forbid circumvention of
technological measures.

  4. Conveying Verbatim Copies.

  You may convey verbatim copies of the Program's source code as you
receive it, in any medium, provided that you conspicuously and
appropriately publish on each copy an appropriate copyright notice;
keep intact all notices stating that this License and any
non-permissive terms added in accord with section 7 apply to the code;
keep intact all notices of the absence of any warranty; and give all
recipients a copy of this License along with the Program.

  You may charge any price or no price for each copy that you convey,
and you may offer support or warranty protection for a fee.

  5. Conveying Modified Source Versions.

  You may convey a work based on the Program, or the modifications to
produce it from the Program, in the form of source code under the
terms of section 4, provided that you also meet all of these conditions:

    a) The work must carry prominent notices stating that you modified
    it, and giving a relevant date.

    b) The work must carry prominent notices stating that it is
    released under this License and any conditions added under section
    7.  This requirement modifies the requirement in section 4 to
    "keep intact all notices".

    c) You must license the entire work, as a whole, under this
    License to anyone who comes into possession of a copy.  This
    License will therefore apply, along with any applicable section 7
    additional terms, to the whole of the work, and all its parts,
    regardless of how they are packaged.  This License gives no
    permission to license the work in any other way, but it does not
    invalidate such permission if you have separately received it.

    d) If the work has interactive user interfaces, each must display
    Appropriate Legal Notices; however, if the Program has interactive
    interfaces that do not display Appropriate Legal Notices, your
    work need not make them do so.

  A compilation of a covered work with other separate and independent
works, which are not by their nature extensions of the covered work,
and which are not combined with it such as to form a larger program,
in or on a volume of a storage or distribution medium, is called an
"aggregate" if the compilation and its resulting copyright are not
used to limit the access or legal rights of the compilation's users
beyond what the individual works permit.  Inclusion of a covered work
in an aggregate does not cause this License to apply to the other
parts of the aggregate.

  6. Conveying Non-Source Forms.

  You may convey a covered work in object code form under the terms
of sections 4 and 5, provided that you also convey the
machine-readable Corresponding Source under the terms of this License,
in one of these ways:

    a) Convey the object code in, or embodied in, a physical product
    (including a physical distribution medium), accompanied by the
    Corresponding Source fixed on a durable physical medium
    customarily used for software interchange.

    b) Convey the object code in, or embodied in, a physical product
    (including a physical distribution medium), accompanied by a
    written offer, valid for at least three years and valid for as
    long as you offer spare parts or customer support for that product
    model, to give anyone who possesses the object code either (1) a
    copy of the Corresponding Source for all the software in the
    product that is covered by this License, on a durable physical
    medium customarily used for software interchange, for a price no
    more than your reasonable cost of physically performing this
    conveying of source, or (2) access to copy the
    Corresponding Source from a network server at no charge.

    c) Convey individual copies of the object code with a copy of the
    written offer to provide the Corresponding Source.  This
    alternative is allowed only occasionally and noncommercially, and
    only if you received the object code with such an offer, in accord
    with subsection 6b.

    d) Convey the object code by offering access from a designated
    place (gratis or for a charge), and offer equivalent access to the
    Corresponding Source in the same way through the same place at no
    further charge.  You need not require recipients to copy the
    Corresponding Source along with the object code.  If the place to
    copy the object code is a network server, the Corresponding Source
    may be on a different server (operated by you or a third party)
    that supports equivalent copying facilities, provided you maintain
    clear directions next to the object code saying where to find the
    Corresponding Source.  Regardless of what server hosts the
    Corresponding Source, you remain obligated to ensure that it is
    available for as long as needed to satisfy these requirements.

    e) Convey the object code using peer-to-peer transmission, provided
    you inform other peers where the object code and Corresponding
    Source of the work are being offered to the general public at no
    charge under subsection 6d.

  A separable portion of the object code, whose source code is excluded
from the Corresponding Source as a System Library, need not be
included in conveying the object code work.

  A "User Product" is either (1) a "consumer product", which means any
tangible personal property which is normally used for personal, family,
or household purposes, or (2) anything designed or sold for incorporation
into a dwelling.  In determining whether a product is a consumer product,
doubtful cases shall be resolved in favor of coverage.  For a particular
product received by a particular user, "normally used" refers to a
typical or common use of that class of product, regardless of the status
of the particular user or of the way in which the particular user
actually uses, or expects or is expected to use, the product.  A product
is a consumer product regardless of whether the product has substantial
commercial, industrial or non-consumer uses, unless such uses represent
the only significant mode of use of the product.

  "Installation Information" for a User Product means any methods,
procedures, authorization keys, or other information required to install
and execute modified versions of a covered work in that User Product from
a modified version of its Corresponding Source.  The information must
suffice to ensure that the continued functioning of the modified object
code is in no case prevented or interfered with solely because
modification has been made.

  If you convey an object code work under this section in, or with, or
specifically for use in, a User Product, and the conveying occurs as
part of a transaction in which the right of possession and use of the
User Product is transferred to the recipient in perpetuity or for a
fixed term (regardless of how the transaction is characterized), the
Corresponding Source conveyed under this section must be accompanied
by the Installation Information.  But this requirement does not apply
if neither you nor any third party retains the ability to install
modified object code on the User Product (for example, the work has
been installed in ROM).

  The requirement to provide Installation Information does not include a
requirement to continue to provide support service, warranty, or updates
for a work that has been modified or installed by the recipient, or for
the User Product in which it has been modified or installed.  Access to a
network may be denied when the modification itself materially and
adversely affects the operation of the network or violates the rules and
protocols for communication across the network.

  Corresponding Source conveyed, and Installation Information provided,
in accord with this section must be in a format that is publicly
documented (and with an implementation available to the public in
source code form), and must require no special password or key for
unpacking, reading or copying.

  7. Additional Terms.

  "Additional permissions" are terms that supplement the terms of this
License by making exceptions from one or more of its conditions.
Additional permissions that are applicable to the entire Program shall
be treated as though they were included in this License, to the extent
that they are valid under applicable law.  If additional permissions
apply only to part of the Program, that part may be used separately
under those permissions, but the entire Program remains governed by
this License without regard to the additional permissions.

  When you convey a copy of a covered work, you may at your option
remove any additional permissions from that copy, or from any part of
it.  (Additional permissions may be written to require their own
removal in certain cases when you modify the work.)  You may place
additional permissions on material, added by you to a covered work,
for which you have or can give appropriate copyright permission.

  Notwithstanding any other provision of this License, for material you
add to a covered work, you may (if authorized by the copyright holders of
that material) supplement the terms of this License with terms:

    a) Disclaiming warranty or limiting liability differently from the
    terms of sections 15 and 16 of this License; or

    b) Requiring preservation of specified reasonable legal notices or
    author attributions in that material or in the Appropriate Legal
    Notices displayed by works containing it; or

    c) Prohibiting misrepresentation of the origin of that material, or
    requiring that modified versions of such material be marked in
    reasonable ways as different from the original version; or

    d) Limiting the use for publicity purposes of names of licensors or
    authors of the material; or

    e) Declining to grant rights under trademark law for use of some
    trade names, trademarks, or service marks; or

    f) Requiring indemnification of licensors and authors of that
    material by anyone who conveys the material (or modified versions of
    it) with contractual assumptions of liability to the recipient, for
    any liability that these contractual assumptions directly impose on
    those licensors and authors.

  All other non-permissive additional terms are considered "further
restrictions" within the meaning of section 10.  If the Program as you
received it, or any part of it, contains a notice stating that it is
governed by this License along with a term that is a further
restriction, you may remove that term.  If a license document contains
a further restriction but permits relicensing or conveying under this
License, you may add to a covered work material governed by the terms
of that license document, provided that the further restriction does
not survive such relicensing or conveying.

  If you add terms to a covered work in accord with this section, you
must place, in the relevant source files, a statement of the
additional terms that apply to those files, or a notice indicating
where to find the applicable terms.

  Additional terms, permissive or non-permissive, may be stated in the
form of a separately written license, or stated as exceptions;
the above requirements apply either way.

  8. Termination.

  You may not propagate or modify a covered work except as expressly
provided under this License.  Any attempt otherwise to propagate or
modify it is void, and will automatically terminate your rights under
this License (including any patent licenses granted under the third
paragraph of section 11).

  However, if you cease all violation of this License, then your
license from a particular copyright holder is reinstated (a)
provisionally, unless and until the copyright holder explicitly and
finally terminates your license, and (b) permanently, if the copyright
holder fails to notify you of the violation by some reasonable means
prior to 60 days after the cessation.

  Moreover, your license from a particular copyright holder is
reinstated permanently if the copyright holder notifies you of the
violation by some reasonable means, this is the first time you have
received notice of violation of this License (for any work) from that
copyright holder, and you cure the violation prior to 30 days after
your receipt of the notice.

  Termination of your rights under this section does not terminate the
licenses of parties who have received copies or rights from you under
this License.  If your rights have been terminated and not permanently
reinstated, you do not qualify to receive new licenses for the same
material under section 10.

  9. Acceptance Not Required for Having Copies.

  You are not required to accept this License in order to receive or
run a copy of the Program.  Ancillary propagation of a covered work
occurring solely as a consequence of using peer-to-peer transmission
to receive a copy likewise does not require acceptance.  However,
nothing other than this License grants you permission to propagate or
modify any covered work.  These actions infringe copyright if you do
not accept this License.  Therefore, by modifying or propagating a
covered work, you indicate your acceptance of this License to do so.

  10. Automatic Licensing of Downstream Recipients.

  Each time you convey a covered work, the recipient automatically
receives a license from the original licensors, to run, modify and
propagate that work, subject to this License.  You are not responsible
for enforcing compliance by third parties with this License.

  An "entity transaction" is a transaction transferring control of an
organization, or substantially all assets of one, or subdividing an
organization, or merging organizations.  If propagation of a covered
work results from an entity transaction, each party to that
transaction who receives a copy of the work also receives whatever
licenses to the work the party's predecessor in interest had or could
give under the previous paragraph, plus a right to possession of the
Corresponding Source of the work from the predecessor in interest, if
the predecessor has it or can get it with reasonable efforts.

  You may not impose any further restrictions on the exercise of the
rights granted or affirmed under this License.  For example, you may
not impose a license fee, royalty, or other charge for exercise of
rights granted under this License, and you may not initiate litigation
(including a cross-claim or counterclaim in a lawsuit) alleging that
any patent claim is infringed by making, using, selling, offering for
sale, or importing the Program or any portion of it.

  11. Patents.

  A "contributor" is a copyright holder who authorizes use under this
License of the Program or a work on which the Program is based.  The
work thus licensed is called the contributor's "contributor version".

  A contributor's "essential patent claims" are all patent claims
owned or controlled by the contributor, whether already acquired or
hereafter acquired, that would be infringed by some manner, permitted
by this License, of making, using, or selling its contributor version,
but do not include claims that would be infringed only as a
consequence of further modification of the contributor version.  For
purposes of this definition, "control" includes the right to grant
patent sublicenses in a manner consistent with the requirements of
this License.

  Each contributor grants you a non-exclusive, worldwide, royalty-free
patent license under the contributor's essential patent claims, to
make, use, sell, offer for sale, import and otherwise run, modify and
propagate the contents of its contributor version.

  In the following three paragraphs, a "patent license" is any express
agreement or commitment, however denominated, not to enforce a patent
(such as an express permission to practice a patent or covenant not to
sue for patent infringement).  To "grant" such a patent license to a
party means to make such an agreement or commitment not to enforce a
patent against the party.

  If you convey a covered work, knowingly relying on a patent license,
and the Corresponding Source of the work is not available for anyone
to copy, free of charge and under the terms of this License, through a
publicly available network server or other readily accessible means,
then you must either (1) cause the Corresponding Source to be so
available, or (2) arrange to deprive yourself of the benefit of the
patent license for this particular work, or (3) arrange, in a manner
consistent with the requirements of this License, to extend the patent
license to downstream recipients.  "Knowingly relying" means you have
actual knowledge that, but for the patent license, your conveying the
covered work in a country, or your recipient's use of the covered work
in a country, would infringe one or more identifiable patents in that
country that you have reason to believe are valid.

  If, pursuant to or in connection with a single transaction or
arrangement, you convey, or propagate by procuring conveyance of, a
covered work, and grant a patent license to some of the parties
receiving the covered work authorizing them to use, propagate, modify
or convey a specific copy of the covered work, then the patent license
you grant is automatically extended to all recipients of the covered
work and works based on it.

  A patent license is "discriminatory" if it does not include within
the scope of its coverage, prohibits the exercise of, or is
conditioned on the non-exercise of one or more of the rights that are
specifically granted under this License.  You may not convey a covered
work if you are a party to an arrangement with a third party that is
in the business of distributing software, under which you make payment
to the third party based on the extent of your activity of conveying
the work, and under which the third party grants, to any of the
parties who would receive the covered work from you, a discriminatory
patent license (a) in connection with copies of the covered work
conveyed by you (or copies made from those copies), or (b) primarily
for and in connection with specific products or compilations that
contain the covered work, unless you entered into that arrangement,
or that patent license was granted, prior to 28 March 2007.

  Nothing in this License shall be construed as excluding or limiting
any implied license or other defenses to infringement that may
otherwise be available to you under applicable patent law.

  12. No Surrender of Others' Freedom.

  If conditions are imposed on you (whether by court order, agreement or
otherwise) that contradict the conditions of this License, they do not
excuse you from the conditions of this License.  If you cannot convey a
covered work so as to satisfy simultaneously your obligations under this
License and any other pertinent obligations, then as a consequence you may
not convey it at all.  For example, if you agree to terms that obligate you
to collect a royalty for further conveying from those to whom you convey
the Program, the only way you could satisfy both those terms and this
License would be to refrain entirely from conveying the Program.

  13. Use with the GNU Affero General Public License.

  Notwithstanding any other provision of this License, you have
permission to link or combine any covered work with a work licensed
under version 3 of the GNU Affero General Public License into a single
combined work, and to convey the resulting work.  The terms of this
License will continue to apply to the part which is the covered work,
but the special requirements of the GNU Affero General Public License,
section 13, concerning interaction through a network will apply to the
combination as such.

  14. Revised Versions of this License.

  The Free Software Foundation may publish revised and/or new versions of
the GNU General Public License from time to time.  Such new versions will
be similar in spirit to the present version, but may differ in detail to
address new problems or concerns.

  Each version is given a distinguishing version number.  If the
Program specifies that a certain numbered version of the GNU General
Public License "or any later version" applies to it, you have the
option of following the terms and conditions either of that numbered
version or of any later version published by the Free Software
Foundation.  If the Program does not specify a version number of the
GNU General Public License, you may choose any version ever published
by the Free Software Foundation.

  If the Program specifies that a proxy can decide which future
versions of the GNU General Public License can be used, that proxy's
public statement of acceptance of a version permanently authorizes you
to choose that version for the Program.

  Later license versions may give you additional or different
permissions.  However, no additional obligations are imposed on any
author or copyright holder as a result of your choosing to follow a
later version.

  15. Disclaimer of Warranty.

  THERE IS NO WARRANTY FOR THE PROGRAM, TO THE EXTENT PERMITTED BY
APPLICABLE LAW.  EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT
HOLDERS AND/OR OTHER PARTIES PROVIDE THE PROGRAM "AS IS" WITHOUT WARRANTY
OF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO,
THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR
PURPOSE.  THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE PROGRAM
IS WITH YOU.  SHOULD THE PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF
ALL NECESSARY SERVICING, REPAIR OR CORRECTION.

  16. Limitation of Liability.

  IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING
WILL ANY COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MODIFIES AND/OR CONVEYS
THE PROGRAM AS PERMITTED ABOVE, BE LIABLE TO YOU FOR DAMAGES, INCLUDING ANY
GENERAL, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE
USE OR INABILITY TO USE THE PROGRAM (INCLUDING BUT NOT LIMITED TO LOSS OF
DATA OR DATA BEING RENDERED INACCURATE OR LOSSES SUSTAINED BY YOU OR THIRD
PARTIES OR A FAILURE OF THE PROGRAM TO OPERATE WITH ANY OTHER PROGRAMS),
EVEN IF SUCH HOLDER OR OTHER PARTY HAS BEEN ADVISED OF THE POSSIBILITY OF
SUCH DAMAGES.

  17. Interpretation of Sections 15 and 16.

  If the disclaimer of warranty and limitation of liability provided
above cannot be given local legal effect according to their terms,
reviewing courts shall apply local law that most closely approximates
an absolute waiver of all civil liability in connection with the
Program, unless a warranty or assumption of liability accompanies a
copy of the Program in return for a fee.

                     END OF TERMS AND CONDITIONS

            How to Apply These Terms to Your New Programs

  If you develop a new program, and you want it to be of the greatest
possible use to the public, the best way to achieve this is to make it
free software which everyone can redistribute and change under these terms.

  To do so, attach the following notices to the program.  It is safest
to attach them to the start of each source file to most effectively
state the exclusion of warranty; and each file should have at least
the "copyright" line and a pointer to where the full notice is found.

    <one line to give the program's name and a brief idea of what it does.>
    Copyright (C) <year>  <name of author>

    This program is free software: you can redistribute it and/or modify
    it under the terms of the GNU General Public License as published by
    the Free Software Foundation, either version 3 of the License, or
    (at your option) any later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program.  If not, see <https://www.gnu.org/licenses/>.

Also add information on how to contact you by electronic and paper mail.

  If the program does terminal interaction, make it output a short
notice like this when it starts in an interactive mode:

    <program>  Copyright (C) <year>  <name of author>
    This program comes with ABSOLUTELY NO WARRANTY; for details type \`show w'.
    This is free software, and you are welcome to redistribute it
    under certain conditions; type \`show c' for details.

The hypothetical commands \`show w' and \`show c' should show the appropriate
parts of the General Public License.  Of course, your program's commands
might be different; for a GUI interface, you would use an "about box".

  You should also get your employer (if you work as a programmer) or school,
if any, to sign a "copyright disclaimer" for the program, if necessary.
For more information on this, and how to apply and follow the GNU GPL, see
<https://www.gnu.org/licenses/>.

  The GNU General Public License does not permit incorporating your program
into proprietary programs.  If your program is a subroutine library, you
may consider it more useful to permit linking proprietary applications with
the library.  If this is what you want to do, use the GNU Lesser General
Public License instead of this License.  But first, please read
<https://www.gnu.org/licenses/why-not-lgpl.html>.
`;var ki=T('<pre class="license-text svelte-16ie8u9"> </pre>'),Si=T('<div class="about svelte-16ie8u9"><h2 class="about-title svelte-16ie8u9">KeY-τ</h2> <div class="about-version svelte-16ie8u9"> </div> <p class="about-desc svelte-16ie8u9">A user interface for the KeY prover family.</p> <div class="about-license-line svelte-16ie8u9">Licensed under <strong> </strong> <button class="license-toggle svelte-16ie8u9"> </button></div> <!></div>');function xi(t,e){fe(e,!0);let n=X(!1);zt(t,{get open(){return e.open},get onclose(){return e.onClose},children:(r,a)=>{var s=Si(),i=b(v(s),2),h=v(i);c(i);var d=b(i,4),l=b(v(d)),u=v(l,!0);c(l);var k=b(l,2),m=v(k,!0);c(k),c(d);var _=b(d,2);{var g=P=>{var f=ki(),y=v(f,!0);c(f),B(()=>W(y,_i)),p(P,f)};H(_,P=>{o(n)&&P(g)})}c(s),B(()=>{W(h,`Version ${Nn.version}`),W(u,Nn.license),W(m,o(n)?"Hide license text":"Show license text")}),z("click",k,()=>O(n,!o(n))),p(r,s)},$$slots:{default:!0}}),ve()}ge(["click"]);var Ti=T('<div class="toolbar-sep svelte-1ld6r3r"></div>'),Ei=Mn('<svg class="tb-icon svelte-1ld6r3r" viewBox="0 0 16 16" fill="none" stroke="currentColor" stroke-width="1.5"></svg>'),Ii=T('<button class="tb-btn svelte-1ld6r3r"><!> </button>'),Ai=T("<!> <!>",1),Ci=T('<div class="toolbar svelte-1ld6r3r"></div>');function Pi(t,e){fe(e,!0);var n=Ci();me(n,21,()=>Vr,r=>r.id,(r,a)=>{var s=Se(),i=ne(s);{var h=l=>{var u=Ai(),k=ne(u);{var m=f=>{var y=Ti();p(f,y)};H(k,f=>{var y;(y=o(a).toolbar)!=null&&y.sep&&f(m)})}var _=b(k,2);{var g=f=>{var y=Se(),F=ne(y);qt(F,()=>o(a).toolbar.component,(D,L)=>{L(D,{get ctx(){return e.ctx}})}),p(f,y)},P=f=>{var y=Ii(),F=v(y);{var D=N=>{var G=Ei();hr(G,()=>o(a).icon,!0),c(G),p(N,G)};H(F,N=>{o(a).icon&&N(D)})}var L=b(F);c(y),B((N,G)=>{var U;y.disabled=N,Fe(y,"title",G),W(L,` ${((U=o(a).toolbar)==null?void 0:U.label)??o(a).label??""}`)},[()=>{var N,G;return!(((G=(N=o(a)).enabled)==null?void 0:G.call(N,e.ctx))??!0)},()=>o(a).shortcut?`${o(a).label} (${Gt(o(a).shortcut)})`:o(a).label]),z("click",y,()=>o(a).run(e.ctx)),p(f,y)};H(_,f=>{var y;(y=o(a).toolbar)!=null&&y.component?f(g):f(P,-1)})}p(l,u)},d=de(()=>{var l,u;return((u=(l=o(a)).visible)==null?void 0:u.call(l,e.ctx))??!0});H(i,l=>{o(d)&&l(h)})}p(r,s)}),c(n),p(t,n),ve()}ge(["click"]);var Ct;class Oi{constructor(){pt(this,Ct,X(0))}get count(){return o(Ge(this,Ct))}notify(){ir(Ge(this,Ct))}}Ct=new WeakMap;const ao="key-tau.recentFiles",Li="keyui.recentFiles",Ni=5,Ri=[{name:"Key files",extensions:["key","proof","sol"]},{name:"All Files",extensions:["*"]}];function Mi(){try{return JSON.parse(localStorage.getItem(ao)??localStorage.getItem(Li)??"[]")}catch{return[]}}var Pt;class Di{constructor(e,n){pt(this,Pt,X(je(Mi())));this.appState=e,this.onError=n}get recent(){return o(Ge(this,Pt))}set recent(e){O(Ge(this,Pt),e,!0)}pushRecent(e){this.recent=[e,...this.recent.filter(n=>n!==e)].slice(0,Ni),localStorage.setItem(ao,JSON.stringify(this.recent))}async activateProof(e){const n=this.appState;n.proof=e;const r=await n.client.proofTreeRoot(e);n.active_node=r.id}async open(e){try{const n=await this.appState.client.load({problemFile:e,includes:null});await this.activateProof(n),this.pushRecent(e)}catch(n){this.onError(n.toString())}}async openPicker(){if(!Ae){const n=await ji();if(n==null)return;try{const r=await this.appState.client.loadKey(n);await this.activateProof(r)}catch(r){this.onError(r.toString())}return}const e=await eo({multiple:!1,directory:!1,filters:Ri});e!=null&&await this.open(e)}async reopenLast(){this.recent.length>0&&await this.open(this.recent[0])}async saveProof(){const e=this.appState;if(e.proof)try{const n=Ae?await Oa({filters:[{name:"Proof files",extensions:["proof"]}]}):window.prompt("Save proof on the server as (absolute path):");n&&await e.client.saveProof(e.proof,n)}catch(n){this.onError(n.toString())}}}Pt=new WeakMap;function ji(){return new Promise(t=>{const e=document.createElement("input");e.type="file",e.accept=".key,.proof,.sol",e.onchange=async()=>{var r;const n=(r=e.files)==null?void 0:r[0];t(n?await n.text():null)},e.oncancel=()=>t(null),e.click()})}var Rn;(function(t){t.WINDOW_RESIZED="tauri://resize",t.WINDOW_MOVED="tauri://move",t.WINDOW_CLOSE_REQUESTED="tauri://close-requested",t.WINDOW_DESTROYED="tauri://destroyed",t.WINDOW_FOCUS="tauri://focus",t.WINDOW_BLUR="tauri://blur",t.WINDOW_SCALE_FACTOR_CHANGED="tauri://scale-change",t.WINDOW_THEME_CHANGED="tauri://theme-changed",t.WINDOW_CREATED="tauri://window-created",t.WEBVIEW_CREATED="tauri://webview-created",t.DRAG_ENTER="tauri://drag-enter",t.DRAG_OVER="tauri://drag-over",t.DRAG_DROP="tauri://drag-drop",t.DRAG_LEAVE="tauri://drag-leave"})(Rn||(Rn={}));async function Fi(t,e){window.__TAURI_EVENT_PLUGIN_INTERNALS__.unregisterListener(t,e),await ot("plugin:event|unlisten",{event:t,eventId:e})}async function qi(t,e,n){var r;const a=(r=void 0)!==null&&r!==void 0?r:{kind:"Any"};return ot("plugin:event|listen",{event:t,target:a,handler:fa(e)}).then(s=>async()=>Fi(t,s))}var Ot;class Gi{constructor(e,n){pt(this,Ot,X(null));this.appState=e,this.onError=n}get confirm(){return o(Ge(this,Ot))}set confirm(e){O(Ge(this,Ot),e,!0)}currentJarPath(){const e=pn(bt);return e.jarPaths[e.flavor]??null}async apply(e,{silent:n=!1}={}){const r=this.appState;try{if(!Ae||e.type==="websocket"){await this.connect(e,null);return}const a=e.type!=="tcp",s=a?this.currentJarPath():null;if(a&&!s){r.serverStatus="disconnected";return}if(e.type==="local-tcp"){const i=e.port,h=await r.client.probeTcp("localhost",i);if(h&&n){await this.connect({type:"tcp",host:"localhost",port:i},null);return}if(h){await this.askExistingOrRestart(e,s,i);return}}await this.connect(e,s)}catch(a){n||this.onError(a.toString()),r.serverStatus="disconnected"}}askExistingOrRestart(e,n,r){return new Promise(a=>{this.confirm={message:`A server is already running on localhost:${r}.`,yes:"Use existing server",no:"Start local JAR (restart)",onYes:async()=>{this.confirm=null,await this.connect({type:"tcp",host:"localhost",port:r},null),a()},onNo:async()=>{this.confirm=null,await this.connect(e,n),a()}}})}async connect(e,n){const r=this.appState;await r.client.connect(e,n),r.proof=null,r.active_node=null;try{const a=await r.client.proofList();if(a.length>0){const s=a[a.length-1];r.proof=s;const i=await r.client.proofTreeRoot(s);r.active_node=i.id,r.proofTreeChanged.notify()}}catch{}}async start(){return this.apply(pn(bt).connection,{silent:!0}),Ae?await qi("prover:status",e=>{this.appState.serverStatus=e.payload.connected?"connected":"disconnected"}):()=>{}}}Ot=new WeakMap;var zi=T('<h2>Error</h2> <pre class="error-pre svelte-1uha8ag"><code> </code></pre>',1),Ui=T('<h2 style="margin:0 0 10px; font-size:15px;">Server already running</h2> <p style="margin:0 0 16px; font-size:13px; opacity:0.8;"> </p> <div class="confirm-row svelte-1uha8ag"><button class="confirm-btn svelte-1uha8ag"> </button> <button class="confirm-btn confirm-primary svelte-1uha8ag"> </button></div>',1),Hi=T('<!> <div class="pane svelte-1uha8ag"><!></div>',1),Yi=T('<div class="app svelte-1uha8ag"><!> <!> <!> <!> <!> <!> <div class="workspace svelte-1uha8ag"></div> <!></div>');function $i(t,e){fe(e,!0);const n=()=>Vn(bt,"$preferences",r),[r,a]=Kn(),s=new ka;let i=je({client:s,proof:null,active_node:null,active_node_status:null,serverStatus:"disconnected",proofTreeChanged:new Oi,capabilities:sn(n().flavor).capabilities});s.onStatusChange=w=>{i.serverStatus=w};let h=X(null),d=X(!1),l=X(!1);const u=w=>O(h,w,!0),k=new Di(i,u),m=new Gi(i,u),_={appState:i,files:k,reportError:u,openPreferences:()=>O(d,!0),openAbout:()=>O(l,!0),quit:()=>ot("quit")};function g(w){var E,q;for(const j of Jr)if(Xr(w,j.shortcut)&&!(!(((E=j.visible)==null?void 0:E.call(j,_))??!0)||!(((q=j.enabled)==null?void 0:q.call(j,_))??!0))){w.preventDefault(),j.run(_);return}}let P=null;ln(async()=>{P=await m.start()}),_o(()=>{P==null||P()}),ke(()=>{const w=n().flavor;i.client.setFlavor(w),i.capabilities=sn(w).capabilities}),ke(()=>{const w=n(),E=document.documentElement;E.style.setProperty("--pref-font-family",w.fonts.global.family),E.style.setProperty("--base-font-size",w.fonts.global.size+"px")});let f=je(Object.fromEntries(dt.map(w=>[w.id,w.defaultFlex]))),y=X(null);function F(w,E){if(!o(y)||E===0)return;const q=o(y).clientWidth;if(q===0)return;const j=dt[w],oe=dt[w+1];if(!j||!oe)return;const K=dt.reduce((Z,$)=>Z+f[$.id],0),re=E/q*K,ue=K*.05,we=f[j.id]+f[oe.id];f[j.id]=Math.max(ue,Math.min(f[j.id]+re,we-ue)),f[oe.id]=we-f[j.id]}var D=Yi();ze("keydown",Yt,g);var L=v(D);ia(L,{get ctx(){return _}});var N=b(L,2);{var G=w=>{zt(w,{open:!0,onclose:()=>O(h,null),children:(E,q)=>{var j=zi(),oe=b(ne(j),2),K=v(oe),re=v(K,!0);c(K),c(oe),B(()=>W(re,o(h))),p(E,j)},$$slots:{default:!0}})};H(N,w=>{o(h)&&w(G)})}var U=b(N,2);{var V=w=>{zt(w,{open:!0,get onclose(){return m.confirm.onNo},closeOnBackdrop:!1,children:(E,q)=>{var j=Ui(),oe=b(ne(j),2),K=v(oe,!0);c(oe);var re=b(oe,2),ue=v(re),we=v(ue,!0);c(ue);var Z=b(ue,2),$=v(Z,!0);c(Z),c(re),B(()=>{W(K,m.confirm.message),W(we,m.confirm.no),W($,m.confirm.yes)}),z("click",ue,function(...ee){var I;(I=m.confirm.onNo)==null||I.apply(this,ee)}),z("click",Z,function(...ee){var I;(I=m.confirm.onYes)==null||I.apply(this,ee)}),p(E,j)},$$slots:{default:!0}})};H(U,w=>{m.confirm&&w(V)})}var Y=b(U,2);yi(Y,{get open(){return o(d)},onApply:w=>m.apply(w),onClose:()=>O(d,!1)});var x=b(Y,2);xi(x,{get open(){return o(l)},onClose:()=>O(l,!1)});var R=b(x,2);Pi(R,{get ctx(){return _}});var C=b(R,2);me(C,23,()=>dt,w=>w.id,(w,E,q)=>{const j=de(()=>Pa(n(),o(E).id));var oe=Hi(),K=ne(oe);{var re=ee=>{ro(ee,{onDrag:I=>F(o(q)-1,I)})};H(K,ee=>{o(q)>0&&ee(re)})}var ue=b(K,2),we=v(ue);{var Z=ee=>{var I=Se(),Q=ne(I);qt(Q,()=>o(E).component,(te,le)=>{le(te,{get appState(){return i}})}),p(ee,I)},$=ee=>{Zn(ee,{children:(I,Q)=>{var te=Se(),le=ne(te);qt(le,()=>o(E).component,(ce,se)=>{se(ce,{get appState(){return i}})}),p(I,te)}})};H(we,ee=>{o(E).chrome==="bare"?ee(Z):ee($,-1)})}c(ue),B(()=>et(ue,`flex: ${f[o(E).id]??""} 1 0; min-width: ${o(E).minWidth??""}px;
                       --pane-font-size: ${o(j).size??""}px; --pane-font-family: ${o(j).family??""};`)),p(w,oe)}),c(C),nt(C,w=>O(y,w),()=>o(y));var S=b(C,2);ua(S,{get appState(){return i},onReconnect:w=>m.apply(w)}),c(D),p(t,D),ve(),a()}ge(["click"]);export{$i as _,ot as i};
