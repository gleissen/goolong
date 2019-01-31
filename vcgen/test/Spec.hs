import Language.IceT.VCGen2

import Test.Hspec
import Test.Hspec.Core.Runner
import Test.Hspec.Core.Formatters

main :: IO ()
main = spec

testPrograms :: [(String, String, Bool)]
testPrograms = [
  ( "bakst-test"
  , "\
    \prog(tmp, \
    \     [decl(ho,map(set(ps),int)), decl(as,set), decl(ps,set)], \
    \     ensures(true), \
    \     seq([for(_,A,ps,r,true,atomic(seq([assign(A,ho,0)]))), \
    \          sym(A,ps,seq([ite(A,2*ref(ho,A)>card(as), \
    \                            seq([for(A,C,as,_,true, seq([atomic(seq([skip]))])), \
    \                                 ite(A,2*ref(ho,A)<card(as), \
    \                                     seq([pre(A,forall([decl(i,int)], \
    \                                                       implies(and([elem(i,ps),here(i)]), \
    \                                                               and([2*ref(ho,i) > card(as)])))), \
    \                                          skip]), \
    \                                     skip)]), \
    \                            skip)]))]))."
  , True
  )
  ]

spec :: IO ()
spec = hspecWith cfg $ do
  describe "test programs" $
    sequence_ $ testPair <$> testPrograms
    
  where
    cfg = defaultConfig { configFormatter = Just silent
                        }
    
testPair :: (String, String, Bool) -> SpecWith ()
testPair (name, str, result) = do
  it name $
    verifyProgram str `shouldReturn` result
