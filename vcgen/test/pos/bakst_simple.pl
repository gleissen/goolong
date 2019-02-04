prog(simple,
     [decl(m,int),decl(q,set),decl(id,map(set(q),int))],
     ensures(forall([decl(i,int)],implies(elem(i,q),ref(id,i)=m))),
     seq([for(_,A,q,r,true,atomic(seq([assign(A,id,0)]))),
          for(m,A,q,rr,forall([decl(i,int)],and([implies(and([elem(i,rr)]),ref(id,i)=m)])),seq([assign(A,id,m,m)]))])).
