module Language.IceT.Pretty (render, pp, pretty) where

import Language.IceT.Types
import Text.PrettyPrint.HughesPJ

class Pretty a where
  pp :: a -> Doc

  pretty :: a -> String
  pretty = renderStyle (style { lineLength = 200 }) . pp

instance VCAnnot a => Pretty (Stmt a) where
  pp stmt = pp_stmt stmt <+> text "//" <+> (text $ show $ stmtData stmt)

pp_stmt (Skip _)         = text "skip" <> semi
pp_stmt (Par x xs _ s _) = text "proctype" <+> text xs <> parens (text x) <> colon
                    $+$ nest 2 (pp s)
pp_stmt (Assign p b q e _) = pp b <+> text ":=" <+> pp e <> semi <+> text "//" <+> text p <+> text "<-" <+> text q
pp_stmt (Seq stmts s) = vcat (pp <$> stmts)
pp_stmt (Atomic s _) = text "<" <+> pp s <+> text ">" <> semi
pp_stmt (Assume p _) = text "assume" <+> pp p
pp_stmt (Assert p _ _) = text "assert" <+> pp p
pp_stmt (If p s1 s2 _) = text "if" <+> parens (pp p) $+$ nest 2 (pp s1) $+$
                    text "else" $+$ (nest 2 (pp s2))
pp_stmt (ForEach x xs _ s _) = text "for" <+> pp x <+> colon <+> pp xs $+$ nest 2 (pp s)
pp_stmt (While x s _) = text "while" <+> text x $+$ nest 2 (pp s)

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

instance Pretty a => Pretty [a] where
  pp as = brackets $ cat $ punctuate (comma <> text " ") (pp <$> as)

instance VCAnnot a => Pretty (Action a) where
  pp (Action scope processes pathProp loc exits stmt) =
    text "Action" <> parens rest
    where
      tupList fa fb l = brackets $
                        cat $
                        punctuate (comma <> text " ")
                        ((\(a,b) -> parens (fa a <> comma <+> fb b)) <$> l)

      rest = vcat [ text "scope = " <> pp scope
                  , text "procs = " <> tupList text text processes
                  , text "path  = " <> pp pathProp
                  , text "loc   = " <> int loc
                  , text "exits = " <> tupList pp int exits
                  , text "stmt  = " <> pp stmt
                  ]

stmtData :: Stmt a -> a
stmtData (Skip a)            = a
stmtData (Par _ _ _ _ a)     = a
stmtData (Assign _ _ _ _ a)  = a
stmtData (Seq _ a)           = a
stmtData (Atomic _ a)        = a
stmtData (Assume _ a)        = a
stmtData (Assert _ _ a)      = a
stmtData (If _ _ _ a)        = a
stmtData (Cases _ _ a)       = a
stmtData (ForEach _ _ _ _ a) = a
stmtData (While _ _ a)       = a
