prog(tmp, 
     [ decl(ho,int),
       decl(as,set)
     ], 
     ensures(true),
     seq([ ite(a, ho>0,
               seq([ for(a,C,as,_,true, seq([atomic(seq([skip]))])),
                     ite(a, ho<0,
                         seq([pre(a,forall([decl(i,int)],
                                           implies(and([elem(i,ps),here(i)]),
                                                   and([ho > 0])))), 
                              skip]),
                         skip)]),
               skip)])
    ).
