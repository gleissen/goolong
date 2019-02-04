prog(tmp,
     [decl(a0,int),
      decl(t,map(set(ps),int)),
      decl(id,map(set(ps),int)),
      decl(xT,map(set(ps),int)),
      decl(x,map(set(ps),int)),
      decl(ho,map(set(ps),int)),
      decl(ready,map(set(ps),int)),
      decl(decided,map(set(ps),int)),
      decl(inst,map(set(ps),int)),
      decl(instance,map(set(ps),int)),
      decl(k,map(set(ps),int)),
      decl(l,map(set(ps),int)),
      decl(m,map(set(ps),int)),
      decl(rwT,map(set(ps),int)),
      decl(rw,map(set(ps),int)),
      decl(rsuccess,map(set(ps),int)),
      decl(rwT,map(set(ps),int)),
      decl(rw,map(set(ps),int)),
      decl(rsuccess,map(set(ps),int)),
      decl(ps,set),
      decl(max,map(set(as),map(int,int))),
      decl(wT,map(set(as),map(int,int))),
      decl(w,map(set(as),map(int,int))),
      decl(success,map(set(as),int)),
      decl(msgType,map(set(as),int)),
      decl(pID,map(set(as),int)),
      decl(pInst,map(set(as),int)),
      decl(pt,map(set(as),int)),
      decl(px,map(set(as),int)),
      decl(as,set)],

     ensures
    (
      forall([decl(a0,int),decl(p1,int),decl(p2,int)],
             implies(and([elem(a0,as),
                          elem(p1,ps),
                          elem(p2,ps),
                          ref(decided,p1)=1,
                          ref(decided,p2)=1,
                          ref(inst,p1)=ref(inst,p2),
                          implies(and([ref(k,p1)>card(as)/2,
                                       ref(k,p2)>card(as)/2]),
                                  and([ref(t,p1)=<ref(ref(wT,a0), ref(inst,p1)),
                                       ref(t,p2)=<ref(ref(wT,a0), ref(inst,p2))])),
                          0=<ref(l,p1),
                          0=<ref(l,p2)]),
                     ref(x,p1)=ref(x,p2)))
    ),

     seq([for(_,A,ps,r,
              true,
              atomic(seq([
                          pre(A,forall([decl(i,int)],implies(elem(i,r),and([ref(t,i)>0,ref(ready,i)=0,ref(decided,i)=0,ref(ho,i)=0,ref(k,i)=0,ref(l,i)=card(as),ref(m,i)=0])))),

                          assign(A,xT,0),
                          assign(A,ho,0),
                          assign(A,ready,0),
                          assign(A,decided,0),
                          assign(A,inst,ref(instance,A)),
                          assume(A,and([ref(t,A)>0,
                                        ref(m,A)=0,
                                        ref(l,A)=card(as),
                                        ref(k,A)=0]))
                         ]))),

          for(_,B,as,r,
              true,
              atomic(seq([
                          pre(B,forall([decl(i,int),decl(j,int)],
                                       implies(elem(j,r),
                                               ref(ref(wT,j),i)=0))),
                          assume(B,forall([decl(i,int),decl(j,int)],
                                          ref(ref(wT,j),i)=0))
                         ]))),

          sym(A,ps,
              seq([for(A,C,as,_,
                       true,
                       seq([atomic(seq([
                                        pre(A,implies(ref(decided,A)=1,
                                                      and([ref(k,A)>card(as)/2,
                                                           ref(ho,A)>card(as)/2,
                                                           ref(ready,A)=1]))),
                                        pre(A,and([ref(k,A)+ref(l,A)+ref(m,A)=card(as),
                                                   ref(k,A)=0,
                                                   ref(decided,A)=0,
                                                   ref(ready,A)=0])),
                                        pre(A,forall([decl(i,int),decl(j,int)],
                                                     implies(and([elem(i,ps),
                                                                  elem(j,as),
                                                                  ref(l,i)>card(as)/2,
                                                                  ref(k,i)=0]),
                                                             ref(ref(wT,j),ref(inst,i))<ref(t,i)))),
                                        pre(A,forall([decl(qa,int),decl(qp,int)],
                                                     implies(and([elem(qa,as),
                                                                  elem(qp,ps),
                                                                  ref(ready,qp)=1,
                                                                  ref(t,qp)=<ref(ref(wT,qa),ref(inst,qp)),
                                                                  ref(k,qp)+ref(l,qp)>card(as)/2]),
                                                             ref(ref(w,qa),ref(inst,qp))=ref(x,qp)))),
                                        assign(A,id,A),
                                        assign(C,pair(msgType,pair(pID,pair(pInst,pair(pt,px)))),
                                               A,pair(0,      pair(id, pair(inst, pair(t, 0))))),
                                        ite(C,ref(msgType,C)=0,
                                            seq([assign(C,success,0),
                                                 ite(C,ref(pt,C)>ref(ref(max,C),ref(pInst,C)),
                                                     seq([assign(C,max,upd(ref(max,C),ref(pInst,C),ref(pt,C))),
                                                          assign(C,success,1)]),
                                                     skip)]),
                                            skip),
                                        ite(C,ref(msgType,C)=1,
                                            seq([assign(C,success,0),
                                                 ite(C,ref(ref(max,C),ref(pInst,C))=<ref(pt,C),
                                                     seq([assign(C,wT,upd(ref(wT,C),ref(pInst,C),ref(pt,C))),
                                                          assign(C,w,upd(ref(w,C),ref(pInst,C),ref(px,C))),
                                                          assign(C,success,1)]),
                                                     skip)]),
                                            skip),
                                        assign(A,pair(rwT,                        pair(rw,                        rsuccess)),
                                               C,pair(ref(ref(wT,C),ref(pInst,C)),pair(ref(ref(w,C),ref(pInst,C)),success))),
                                        ite(A,ref(rsuccess,A)=1,
                                            seq([assign(A,ho,ref(ho,A)+1)]),
                                            skip),
                                        ite(A,ref(xT,A)=<ref(rwT,A),
                                            seq([assign(A,xT,ref(rwT,A)),
                                                 assign(A,x,ref(rw,A))]),
                                            skip)
                                       ]))
                           ])),

                   ite(A,2*ref(ho,A)>card(as),
                       seq([
                            pre(A,forall([decl(i,int),decl(j,int)],
                                         implies(and([elem(i,ps),
                                                      elem(j,as),
                                                      ref(l,i)>card(as)/2,
                                                      ref(k,i)=0]),
                                                 ref(ref(wT,j),ref(inst,i))<ref(t,i)))),
                            pre(A,and([ref(decided,A)=0,
                                       ref(ready,A)=1,
                                       ref(k,A)=0,
                                       ref(ho,A)=<ref(k,A),
                                       ref(k,A)+ref(l,A)+ref(m,A)=card(as)])),
                            pre(A,implies(ref(decided,A)=0,
                                          and([ref(k,A)>card(as)/2,
                                               ref(ho,A)>card(as)/2,
                                               ref(ready,A)=1]))),
                            pre(A,forall([decl(qa,int),decl(qp,int)],
                                         implies(and([elem(qa,as),
                                                      elem(qp,ps),
                                                      ref(ready,qp)=1,
                                                      ref(t,qp)=<ref(ref(wT,qa),ref(inst,qp)),
                                                      ref(k,qp)+ref(l,qp)>card(as)/2]),
                                                 ref(ref(w,qa),ref(inst,qp))=ref(x,qp)))),
                            assign(A,ho,0),
                            assign(A,ready,1),

                            for(A,C,as,_,
                                true,
                                seq([atomic(seq([
                                                 pre(A,and([ref(ready,A)=1,
                                                            ref(decided,A)=0,
                                                            ref(ho,A)=<ref(k,A),
                                                            ref(k,A)+ref(l,A)+ref(m,A)=card(as)])),
                                                 pre(A,forall([decl(qa,int),decl(qp,int)],
                                                              implies(and([elem(qa,as),
                                                                           elem(qp,ps),
                                                                           ref(ready,qp)=1,
                                                                           ref(t,qp)=<ref(ref(wT,qa),ref(inst,qp)),
                                                                           ref(k,qp)+ref(l,qp)>card(as)/2]),
                                                                      ref(ref(w,qa),ref(inst,qp))=ref(x,qp)))),
                                                 pre(A,forall([decl(i,int),decl(j,int)],
                                                              implies(and([elem(i,ps),
                                                                           elem(j,as),
                                                                           ref(l,i)>card(as)/2,
                                                                           ref(k,i)=0]),
                                                                      ref(ref(wT,j),ref(inst,i))<ref(t,i)))),
                                                 pre(A,implies(ref(decided,A)=1,
                                                               and([ref(k,A)>card(as)/2,
                                                                    ref(ho,A)>card(as)/2,
                                                                    ref(ready,A)=1]))),

                                                 assume(A,elem(a0,as)),
                                                 assume(A,forall([decl(i,int)],
                                                                 implies(and([elem(i,ps),
                                                                              ref(ready,i)=1,
                                                                              ref(k,i)+ref(l,i)>card(as)/2,
                                                                              ref(ready,A)=1]),
                                                                         and([ref(t,i)=<ref(xT,A),
                                                                              0<ref(xT,A)])))),
                                                 assume(A,forall([decl(i,int)],
                                                                 implies(ref(t,i)=ref(t,A),
                                                                         i=A))),
                                                 assume(A,forall([decl(i,int)],
                                                                 implies(and([elem(i,ps),
                                                                              ref(l,i)>card(as)/2]),
                                                                         or([ref(ready,A)=0,
                                                                             ref(t,A)<ref(t,i)])))),
                                                 assume(A,implies(and([0<ref(xT,A)]),
                                                                  and([ref(x,A)=ref(ref(w,a0),ref(inst,A)),
                                                                       ref(xT,A)=ref(ref(wT,a0),ref(inst,A))]))),

                                                 assign(C,pair(msgType,pair(pID,pair(pInst,pair(pt,px)))),
                                                        A,pair(1,      pair(id,  pair(inst,pair(t, x))))),
                                                 ite(C,ref(msgType,C)=0,
                                                     seq([assign(C,success,0),
                                                          ite(C,ref(pt,C)>ref(ref(max,C),ref(pInst,C)),
                                                              seq([assign(C,max,upd(ref(max,C),ref(pInst,C),ref(pt,C))),
                                                                   assign(C,success,1)]),
                                                              skip)]),
                                                     skip),
                                                 ite(C,ref(msgType,C)=1,
                                                     seq([assign(C,success,0),
                                                          ite(C,ref(ref(max,C),ref(pInst,C))=<ref(pt,C),
                                                              seq([assign(C,wT,upd(ref(wT,C),ref(pInst,C),ref(pt,C))),
                                                                   assign(C,w,upd(ref(w,C),ref(pInst,C),ref(px,C))),
                                                                   assign(C,success,1)]),
                                                              skip)]),
                                                     skip),
                                                 assign(A,pair(rwT,                        pair(rw,                        rsuccess)),
                                                        C,pair(ref(ref(wT,C),ref(pInst,C)),pair(ref(ref(w,C),ref(pInst,C)),success))),
                                                 ite(A,ref(rsuccess,A)=1,
                                                     seq([assign(A,ho,ref(ho,A)+1),
                                                          assign(A,k,ref(k,A)+1),
                                                          assign(A,l,ref(l,A)-1)]),
                                                     skip)
                                                ]))
                                    ])),

                            ite(A,2*ref(ho,A)>card(as),
                                seq([
                                     pre(A,implies(ref(decided,A)=1,
                                                   and([ref(k,A)>card(as)/2,
                                                        ref(ho,A)>card(as)/2,
                                                        ref(ready,A)=1]))),
                                     pre(A,forall([decl(i,int),decl(j,int)],
                                                  implies(and([elem(i,ps),
                                                               elem(j,as),
                                                               ref(l,i)>card(as)/2,
                                                               ref(k,i)=0]),
                                                          ref(ref(wT,j),ref(inst,i))<ref(t,i)))),
                                     pre(A,and([ref(ready,A)=1,
                                                ref(decided,A)=1,
                                                ref(ho,A)=<ref(k,A),
                                                ref(k,A)+ref(l,A)+ref(m,A)=card(as)])),
                                     pre(A,forall([decl(qa,int),decl(qp,int)],
                                                  implies(and([elem(qa,as),
                                                               elem(qp,ps),
                                                               ref(ready,qp)=1,
                                                               ref(t,qp)=<ref(ref(wT,qa),ref(inst,qp)),
                                                               ref(k,qp)+ref(l,qp)>card(as)/2]),
                                                          ref(ref(w,qa),ref(inst,qp))=ref(x,qp)))),

                                     assign(A,decided,1)]),
                                seq([
                                     pre(A,ref(decided,A)=0)
                                    ]))
                           ]),
                       seq([
                            pre(A,ref(decided,A)=0)
                           ]))
                  ]))
         ])).
