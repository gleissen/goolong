prog(tmp,
     [decl(px,map(set(ps),int)),
      decl(ps,set),
      decl(qid,map(set(qs),int)),
      decl(y,map(set(qs),int)),
      decl(qid,map(set(qs),int)),
      decl(y,map(set(qs),int)),
      decl(qs,set)],

     ensures(true),

     sym(B,qs,
         seq([for(B,C,ps,_,
                  true,
                  seq([atomic(seq([pre(B, ref(y,B) = 1),
                                   assign(B,pair(qid,y),
                                          C,pair(C,1))])),
                       atomic(seq([assign(C,px,B,y),
                                   assert(C,ref(px,C) = 1)
                                  ]))]))]))).
