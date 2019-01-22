prog(tmp,

     [decl(ho,map(set(ps),int)),
      decl(ps,set),
      decl(as,set)
     ],

     ensures(true),

     sym(A,ps,
         seq([for(A,C,as,_,
                  true,
                  skip),

              ite(A,2*ref(ho,A)<card(as),
                  seq([pre(A,forall([decl(i,int)],
                                    implies(and([elem(i,ps),
                                                 here(i)]),
                                            2*ref(ho,i)>card(as)))),
                       skip]),
                  skip)]))).
