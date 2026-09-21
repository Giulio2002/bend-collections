import * as B from "./bend.ts";
const book=B.book_nil();
await B.book_load(book,process.argv[2],"",new Map());
const flagged=Object.entries(book.tlds).filter(([k,t])=>t.$==="Def"&&(t.u===true||k.includes("~"))).map(([k,t])=>({name:k,explicitUnsafe:t.u===true,templateInstance:k.includes("~")}));
console.log(JSON.stringify({file:process.argv[2],flagged,explicitUnsafe:flagged.filter(x=>x.explicitUnsafe).length,templateInstances:flagged.filter(x=>x.templateInstance).length},null,2));
