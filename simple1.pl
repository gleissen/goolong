prog(tmp,
     [decl(x,map(set(qs),int)),
      decl(qs,set),
      decl(ps,set)
      ],

     ensures(forall([decl(i,int)], implies(elem(i,qs), ref(x,i) = 1))),

     sym(P,ps,
         for(_,Q,qs,rr,
             true,
             atomic(seq([pre(Q, forall([decl(i,int)],
                                       implies(and([elem(i,qs),
                                                    elem(i,rr)]),
                                               ref(x,i) = 1))),
                         assign(Q, x, 1)]))))).

