{-# LANGUAGE RecordWildCards #-}
module Language.IceT.Pretty (render, pp) where

import Language.IceT.Types
import Text.PrettyPrint.HughesPJ
import qualified Data.Map.Strict as M

class Pretty a where
  pp :: a -> Doc

instance Pretty (Stmt a) where
  pp (Skip _)         = text "skip" <> semi
  pp (Par x xs _ s _) = text "proctype" <+> text xs <> parens (text x) <> colon
                        $+$ nest 2 (pp s)
  pp (Assign p b q e _) = pp b <+> text ":=" <+> pp e <> semi <+> text "//" <+> text p <+> text "<-" <+> text q
  pp (Seq stmts s) = vcat (pp <$> stmts)
  pp (Atomic s _) = text "<" <+> pp s <+> text ">" <> semi
  pp (Assume p _) = text "assume" <+> pp p
  pp (Assert p _ _) = text "assert" <+> pp p
  pp (If p s1 s2 _) = text "if" <+> parens (pp p) $+$ nest 2 (pp s1) $+$
                      text "else" $+$ (nest 2 (pp s2))
  pp (ForEach x xs _ s _) = text "for" <+> pp x <+> colon <+> pp xs $+$ nest 2 (pp s)
  pp (While x s _) = text "while" <+> text x $+$ nest 2 (pp s)

instance Pretty (Prop a) where
  pp TT = text "true"
  pp FF = text "false"
  pp (Atom r e1 e2) = parens (pp e1 <+> pp r <+> pp e2)
  pp (Not p) = text "¬" <> parens (pp p)
  pp (And ps) = text "⋀" <> brackets (vcat (punctuate comma (map pp ps)))
  pp (Or ps) = text "∨" <> brackets (hcat (punctuate comma (map pp ps)))
  pp (p :=>: q) = pp p <+> text "=>" <+> pp q
  pp (Forall xs p) = text "∀" <> hcat (punctuate comma (map pp xs)) <> text "."
                 <+> pp p
  pp (Exists xs p) = text "∃" <> hcat (punctuate comma (map pp xs)) <> text "."
                 <+> pp p
  pp (Here e) = text "here" <> parens (pp e)
  pp (NonDetProp) = text "*"

  pp (Prop e) = pp e
  pp (PVar id) = text id
  pp (Let binds p) = text "let" <+> (parens $ cat $ punctuate comma (helper <$> binds)) <+> text "in" <+> pp p
    where
      helper (binder,expr) = pp binder <+> text "=" <+> pp expr

instance Pretty Rel where
  pp Eq = equals
  pp Le = text "≤"
  pp Lt = text "<"
  pp Gt = text ">"
  pp SetMem = text "∈"

instance Pretty (Expr a) where
  pp (Const i) = int i
  pp (EmptySet) = text "{}"
  pp (NonDetValue) = text "*"
  pp (Var x) = text x
  pp (Select e1 e2) = pp e1 <> brackets (pp e2)
  pp (Store e1 e2 e3) = pp e1 <> brackets (pp e2 <+> text ":=" <+> pp e3)
  pp (Bin o e1 e2) = pp e1 <+> pp o <+> pp e2
  pp (Ite p e1 e2) = pp p <+> text "?" <+> pp e1 <+> text ":" <+> pp e2
  pp (PExpr p)     = text "Prop" <> parens (pp p)
  pp (Size e)      = text "|" <> pp e <> text "|"

instance Pretty Op where
  pp Plus = text "+"
  pp Minus = text "-"
  pp SetSubSingle = text "\\"
  pp SetAdd = text "++"
  pp Mul = text "*"
  pp Div = text "/"

instance Pretty Binder where
  pp (Bind x t) = text x <> colon <> pp t
instance Pretty Sort where
  pp Int = text "int"
  pp Set = text "set"
  pp (Map i t) = pp i <+> text "->" <+> pp t
instance Pretty Index where
  pp (SetIdx i) = text i
  pp IntIdx = text "int"


instance Pretty (Card a) where
  pp (Card{..}) = (text cardName) <> (parens $ hcat $ punctuate comma elems)
    where
      elems = ids ++ [pp cardProp]
      ids = text <$> [cardOwner, cardId, cardElem]

instance Pretty (Program a) where
  pp (Prog{..}) = vcat $ [ text "::: decls :::"
                         , vcat $ pp <$> decls
                         , text "::: cardinalities :::"
                         , vcat $ pp <$> cardDecls
                         , text "::: program :::"
                         , pp prog
                         , text "::: ensures :::"
                         , pp ensures
                         ]

instance (Pretty a, Pretty b) => Pretty (a,b) where
  pp (a,b) = (parens3 $ pp a) <+> text ", " <+> (parens3 $ pp b)
    where
      parens3 = parens . parens . parens

instance (Pretty a, Pretty b, Pretty c) => Pretty (a,b,c) where
  pp (a,b,c) = (parens3 $ pp a) <+> text ", " <+> (parens3 $ pp b) <+> text ", " <+> (parens3 $ pp c)
    where
      parens3 = parens . parens . parens

instance Pretty Int where
  pp = int

instance (Pretty a) => Pretty [a] where
  pp l = brackets $ cat $ punctuate (text ", ") (pp <$> l)

instance Pretty (VCState a) where
  pp (VCState{..}) = vcat [ text "type env:" <+> map2doc tenv
                          , text "constrs:" <+> map2docf text constrs
                          , text "ictr:" <+> int ictr
                          , text "freshed:" <+> pp freshed
                          , text "invs:" <+> pp invs
                          , text "cards:" <+> pp cards
                          , text "gather:" <+> (text $ show gather)
                          ]
    where
      map2doc :: (Pretty a) => M.Map String a -> Doc
      map2doc = map2docf pp

      map2docf :: (a -> Doc) -> M.Map String a -> Doc
      map2docf f m =
        let items = M.toList m
        in parens . cat $ punctuate (text ", ") $ (\(k,v) -> text k <+> text "->" <+> f v) <$> items

