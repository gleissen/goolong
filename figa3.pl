prog(tmp,
     [decl(pv,map(set(ps),int)),
      decl(px,map(set(ps),int)),
      decl(ps,set),
      decl(qid,map(set(qs),int)),
      decl(y,map(set(qs),int)),
      decl(qid,map(set(qs),int)),
      decl(y,map(set(qs),int)),
      decl(qs,set)],

     ensures(forall([decl(i,int)],
                    implies(elem(i,qs),ref(y,i)=1))),

     seq([for(_,A,ps,r,
              true,
              atomic(seq([assign(A,pv,1)]))),

          sym(B,qs,
              seq([for(B,C,ps,_,
                       true,
                       seq([atomic(seq([pre(B, ref(y,B) = 1),
                                        assign(B,pair(qid,y),
                                               C,pair(C,pv))])),
                            atomic(seq([assign(C,px,B,y)]))]))]))])).
