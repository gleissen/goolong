import Language.IceT.VCGen2

import Test.Hspec
import Test.Hspec.Core.Runner

main :: IO ()
main = spec

testPrograms :: [(String, String, Bool)]
testPrograms = [
  ( "bakst-test"
  , "\
    \prog(tmp, \
    \     [decl(ho,map(set(ps),int)), \
    \      decl(as,set), \
    \      decl(ps,set)], \
    \     ensures(true), \
    \     seq([for(_,A,ps,r,true,atomic(seq([assign(A,ho,0)]))), \
    \          sym(A,ps,seq([ite(A,2*ref(ho,A)>card(as), \
    \                            seq([for(A,C,as,_,true, seq([atomic(seq([skip]))])), \
    \                                 ite(A,2*ref(ho,A)>card(as), \
    \                                     seq([pre(A,forall([decl(i,int)], \
    \                                                       implies(and([elem(i,ps),here(i)]), \
    \                                                               and([2*ref(ho,i)>card(as)])))), \
    \                                          skip]), \
    \                                     skip)]), \
    \                            skip)]))]))."
  , True
  ),
  ( "fig-a3"
  , "\
    \prog(tmp, \
    \[decl(px,map(set(ps),int)), \
    \ decl(ps,set), \
    \ decl(qid,map(set(qs),int)), \
    \ decl(y,map(set(qs),int)), \
    \ decl(qid,map(set(qs),int)), \
    \ decl(y,map(set(qs),int)), \
    \ decl(qs,set)], \
    \ensures(true), \
    \sym(B,qs, \
    \    seq([for(B,C,ps,_, \
    \             true, \
    \             seq([atomic(seq([pre(B, ref(y,B) = 1), \
    \                              assign(B,pair(qid,y), \
    \                                     C,pair(C,1))])), \
    \                  atomic(seq([assign(C,px,B,y), \
    \                              assert(C,ref(px,C) = 1) \
    \                             ]))]))])))."
   , True
   )
  ]

spec :: IO ()
spec = hspecWith cfg $ do
  describe "test programs" $
    sequence_ $ testPair <$> testPrograms
    
  where
    cfg = defaultConfig
    
testPair :: (String, String, Bool) -> SpecWith ()
testPair (name, str, result) = do
  it name $
    verifyProgram str `shouldReturn` result
