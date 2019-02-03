prog(tmp,
     [decl(f0,int),
      decl(myTerm,map(set(fs),int)),
      decl(voted,map(set(fs),int)),
      decl(votedFor,map(set(fs),int)),
      decl(myVote,map(set(fs),int)),
      decl(votes,map(set(fs),map(int,int))),
      decl(resID,map(set(fs),int)),
      decl(t,map(set(fs),int)),
      decl(fs,set),
      decl(term,map(set(cs),int)),
      decl(id,map(set(cs),int)),
      decl(vote,map(set(cs),int)),
      decl(count,map(set(cs),int)),
      decl(isLeader,map(set(cs),int)),
      decl(k,map(set(cs),int)),
      decl(l,map(set(cs),int)),
      decl(cs,set)],

     ensures
    (
      forall([decl(i,int),
              decl(j,int)],
             implies(and([elem(i,cs),
                          elem(j,cs),
                          ref(term,i)=ref(term,j),
                          ref(isLeader,j)=1,
                          ref(isLeader,i)=1]),
                     i=j))
    ),

     seq([for(_,A,fs,r,
              true,
              atomic(seq([assign(A,voted,0)]))),


          for(_,B,cs,r,
              true,
              atomic(seq([assume(B,forall([decl(i,int)],
                                          and([ref(k,i)=card(fs),
                                               ref(l,i)=0]))),
                          pre(B, forall([decl(i,int)],
                                        implies(elem(i,r),
                                                and([ref(k,i)=card(fs),
                                                     ref(l,i)=0,
                                                     ref(count,i)=0,
                                                     ref(isLeader,i)=0])))),
                          assign(B,isLeader,0),
                          assign(B,count,0)]))),

          sym(A,fs,
              seq([for(A,C,cs,_,
                       true,
                       seq([atomic(seq([assign(A,myVote,0),
                                        pre(C,forall([decl(i,int)],
                                                     implies(elem(i,cs),
                                                             and([ref(k,i)+ref(l,i)=<card(fs),
                                                                  ref(count,i)=ref(l,i)])))),
                                        pre(B,forall([decl(i,int)],
                                                     implies(and([elem(i,cs),
                                                                  ref(isLeader,i)=1]),
                                                             card(fs)<ref(count,i)*2))),
                                        assign(C,id,C),
                                        assign(A,pair(resID,t),
                                               C,pair(id,term)),
                                        ite(A,ref(t,A)>ref(myTerm,A),
                                            seq([assign(A,myTerm,ref(t,A)),
                                                 assign(A,voted,0),
                                                 assign(A,votedFor,0),
                                                 ite(A,and([ref(myTerm,A)=<ref(t,A),
                                                            or([ref(voted,A)=0,
                                                                ref(votedFor,A)=ref(resID,A)])]),
                                                     seq([assign(A,voted,1),
                                                          assign(A,votedFor,ref(resID,A)),
                                                          assign(A,votes,upd(ref(votes,A),ref(myTerm,A),ref(resID,A))),
                                                          assign(A,myVote,1)]),
                                                     skip)]),
                                            seq([ite(A,and([ref(myTerm,A)=<ref(t,A),
                                                            or([ref(voted,A)=0,
                                                                ref(votedFor,A)=ref(resID,A)])]),
                                                     seq([assign(A,voted,1),
                                                          assign(A,votedFor,ref(resID,A)),
                                                          assign(A,votes,upd(ref(votes,A),ref(myTerm,A),ref(resID,A))),
                                                          assign(A,myVote,1)]),
                                                     skip)])),
                                        assign(C,vote,A,myVote),
                                        ite(C,ref(vote,C)=1,
                                            seq([assign(C,count,ref(count,C)+1)]),
                                            skip),
                                        ite(C,and([and([ref(vote,C)=1,
                                                        ref(votedFor,A)=C]),
                                                   ref(term,C)=ref(myTerm,A)]),
                                            seq([assign(C,l,ref(l,C)+1),
                                                 assign(C,k,ref(k,C)-1)]),
                                            skip)]))])),

                   for(_,B,cs,r,
                       true,
                       atomic(seq([assume(B,elem(f0,fs)),
                                   assume(B,forall([decl(i,int),decl(j,int)],
                                                   implies(and([elem(i,cs),
                                                                elem(j,cs),
                                                                ref(l,i)>card(fs)/2,
                                                                ref(l,j)>card(fs)/2]),
                                                           and([ref(ref(votes,f0),ref(term,i))=i,
                                                                ref(ref(votes,f0),ref(term,j))=j])))),
                                   pre(B,forall([decl(i,int)],
                                                implies(elem(i,cs),
                                                        and([ref(k,i)+ref(l,i)=<card(fs),
                                                             ref(count,i)=ref(l,i)])))),
                                   pre(B,forall([decl(i,int),decl(j,int)],
                                                implies(and([elem(i,cs),
                                                             elem(j,cs),
                                                             ref(count,i)>card(fs)/2,
                                                             ref(count,j)>card(fs)/2,
                                                             ref(term,i)=ref(term,j),
                                                             ref(isLeader,j)=1,
                                                             ref(isLeader,i)=1]),
                                                        i=j))),
                                   pre(B,forall([decl(i,int)],
                                                implies(and([elem(i,cs),
                                                             ref(isLeader,i)=1]),
                                                        card(fs)<ref(count,i)*2))),
                                   ite(B,2*ref(count,B)>card(fs),
                                       seq([assign(B,isLeader,1)]),
                                       skip)
                                  ])))

                   ]))])).