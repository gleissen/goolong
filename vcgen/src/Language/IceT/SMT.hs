module Language.IceT.SMT ( smt
                         , smtS
                         , createSMTQuery
                         ) where

import Language.IceT.Types
import Text.PrettyPrint.HughesPJ

class SMT a where
  smt :: a -> Doc

  smtS :: a -> String
  smtS = renderStyle (style { lineLength = 200 }) . smt

instance SMT (Prop a) where
  smt TT             = text "true"
  smt FF             = text "false"
  smt (Atom r e1 e2) = parens (smt r <+> smt e1 <+> smt e2)
  smt (Not p)        = parens (text "not" <+> (smt p))
  smt (And ps)       = parens (text "and" <+> vcat (fmap smt ps))
  smt (Or ps)        = parens (text "or"  $$ vcat (fmap smt ps))
  smt (p :=>: q)     = parens (text "=>" <+> (smt p $+$ smt q))
  smt (Forall xs p)  = parens (text "forall" <+> vcat [parens (vcat (fmap smt xs)), smt p])
  smt (Exists xs p)  = parens (text "exists" <+> vcat [parens (vcat (fmap smt xs)), smt p])
  smt (Let xs p)     = parens (text "let" <+> b $+$ smt p)
    where
      b = parens (vcat [parens (text (bvar x) <+> smt e) | (x,e) <- xs])
  smt (Prop e)       = smt e
  smt NonDetProp     = error "NonDetProp"
  smt (Here _)       = error "Here"
  smt (PVar _)       = error "PVar"

instance SMT Binder where
  smt b = parens (text (bvar b) <+> smt (bsort b))

instance SMT Index where
  smt _ = smt Int

instance SMT Sort where
  smt Bool      = text "Bool"
  smt Int       = text "Int"
  smt Set       = text "Set"
  smt (Map s t) = parens (text "Array" <+> smt s <+> smt t)

instance SMT (Expr a) where
  smt NonDetValue   = error "nondetvalue"
  smt (Const i)     = int i
  smt (Var x)       = text x
  smt (Bin o e1 e2) = parens (smt o <+> smt e1 <+> smt e2)
  smt (Select x y)  = parens (text "select" <+> smt x <+> smt y)
  smt (Store x y z) = parens (text "store" <+> smt x <+> smt y <+> smt z)
  smt (Size e)      = parens (text "set_size" <+> smt e)
  smt EmptySet      = text "set_emp"
  smt (Ite p x y)   = parens (text "ite" <+> smt p $+$ smt x $+$ smt y)
  smt (PExpr e)     = smt e

instance SMT Op where
  smt Plus         = text "+"
  smt Minus        = text "-"
  smt SetSubSingle = text "set_minus"
  smt SetAdd       = text "set_add"
  smt Mul          = text "*"
  smt Div          = text "/"
  
instance SMT Rel where
  smt Eq     = text "="
  smt Lt     = text "<"
  smt Gt     = text ">"
  smt Le     = text "<="
  smt SetMem = text "set_mem"
  smt SetSub = text "set_sub"

prelude :: Doc
prelude = vcat $ text <$> ls
  where
    ls = [ "(define-sort Elt () Int)"
         , "(define-sort Set () (Array Elt Bool))"
         , "(define-sort IntMap () (Array Elt Elt))"
         , "(define-fun set_emp () Set ((as const Set) false))"
         , "(define-fun set_mem ((x Elt) (s Set)) Bool (select s x))"
         , "(define-fun set_add ((s Set) (x Elt)) Set  (store s x true))"
         , "(define-fun set_cap ((s1 Set) (s2 Set)) Set ((_ map and) s1 s2))"
         , "(define-fun set_cup ((s1 Set) (s2 Set)) Set ((_ map or) s1 s2))"
         , "(define-fun set_com ((s Set)) Set ((_ map not) s))"
         , "(define-fun set_dif ((s1 Set) (s2 Set)) Set (set_cap s1 (set_com s2)))"
         , "(define-fun set_sub ((s1 Set) (s2 Set)) Bool (= set_emp (set_dif s1 s2)))"
         , "(define-fun set_minus ((s1 Set) (x Elt)) Set (set_dif s1 (set_add set_emp x)))"
         , "(declare-fun set_size (Set) Int)"
         ]

checkValid :: Prop a -> Doc
checkValid f = parens (text "assert" <+> smt (Not f)) $+$ text "(check-sat)"

declareConsts :: [Binder] -> Doc
declareConsts bs =
  vcat $ [ parens (text "declare-const" <+> text x <+> smt s)
         | (Bind x s) <- bs
         ]

createPCs :: [Id] -> Doc
createPCs pss = declareConsts [ Bind (pcName ps) pcType | ps <- pss ]

createSMTQuery :: [Binder]      -- binders defined in the program
               -> [Id]          -- names of the symmetric sets
               -> Prop a        -- verification condition
               -> String        -- Output in SMT2 input format
createSMTQuery bs pss vc =
  render $ vcat $ prelude : declareConsts bs : createPCs pss : [checkValid vc]
