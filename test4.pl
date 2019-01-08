prog(tmp, 
     [ decl(ho,map(set(ps),int)),
       decl(as,set), 
       decl(ps,set)
     ], 
     ensures(true),
     seq([pre(A,false), 
          skip])).
