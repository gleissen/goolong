prog(tmp, 
     [ decl(ho,map(set(ps),int)),
       decl(as,set), 
       decl(ps,set)
     ], 
     ensures(true),
     seq([ 
           sym(A,ps,seq([ ite(A,2*ref(ho,A)>card(as),
                              seq([ 
                                    ite(A,2*ref(ho,A)<card(as),
                                        seq([pre(A,forall([decl(i,int)],
                                                          implies(and([elem(i,ps),here(i)]),
                                                                  and([2*ref(ho,i) > card(as)])))), 
                                             skip]),
                                        skip)]),
                              skip)]))])).
