prog(tmp,
     [decl(ho,map(set(ps),int)),
      decl(ps,set),
      decl(as,set)
     ], 
     ensures(true), 
     seq([sym(A,ps,seq([seq([for(A,C,as,_,true,seq([skip])),
                             ite(A,2*ref(ho,A)<card(as),
                                 seq([pre(A,forall([decl(i,int)],implies(and([elem(i,ps), here(i)]),
                                                                         and([2*ref(ho,i)>card(as)])))),
                                      skip
                                     ]),
                                 skip)
                            ])
                       ]))
         ])).

