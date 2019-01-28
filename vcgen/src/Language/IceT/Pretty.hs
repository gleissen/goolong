{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ConstraintKinds #-}

module Language.IceT.Pretty (pretty) where

import Prelude hiding ((<>))
import Language.IceT.Types
import Text.PrettyPrint.HughesPJ

class Pretty a where
  pp :: a -> Doc

  pretty :: a -> String
  pretty = renderStyle (style { lineLength = 200 }) . pp

instance Pretty (Stmt a) where
  pp (Skip _)              = text "skip" <> semi
  pp (Par x xs _ s _)      = text "proctype" <+> text xs <> parens (text x) <> colon $+$ nest 2 (pp s)
  pp (Assign p b q e _)    = pp b <+> text ":=" <+> pp e <> semi <+> text "//" <+> text p <+> text "<-" <+> text q
  pp (Seq stmts s)         = vcat (pp <$> stmts)
  -- pp (Atomic {..})         = text "<" <+>
  --                            brackets (int atomicLabel) <+>
  --                            pp atomicPost <+> text "::"
  --                            <+> pp atomicStmt <+> text ">"
  --                            <> semi
  pp (Atomic {..})         = text "atomic" <> brackets (int atomicLabel)
  pp (Assume p _)          = text "assume" <+> pp p
  pp (Assert p _ _)        = text "assert" <+> pp p
  pp (If p s1 s2 _)        = text "if" <+> parens (pp p) $+$ nest 2 (pp s1) $+$ text "else" $+$ (nest 2 (pp s2))
  pp (ForEach x xs _ s _)  = text "for" <+> pp x <+> colon <+> pp xs $+$ nest 2 (pp s)
  pp (While x s _)         = text "while" <+> text x $+$ nest 2 (pp s)
  pp (Cases{..})           = text "switch" <> parens (cat $ punctuate (comma <+> text " ")
                                                      [ pp casesExpr
                                                      , cat $ punctuate (comma <+> text " ") (pp <$> caseList)
                                                      ])

instance Pretty (Case a) where
  pp (Case{..}) = pp caseGuard <> text ":" <+> pp caseStmt

instance Pretty (Prop a) where
  pp TT             = text "true"
  pp FF             = text "false"
  pp (Atom r e1 e2) = parens (pp e1 <+> pp r <+> pp e2)
  pp (Not p)        = text "¬" <> parens (pp p)
  pp (And ps)       = text "⋀" <> brackets (cat (punctuate (text ", ") (map pp ps)))
  pp (Or ps)        = text "∨" <+> brackets (cat (punctuate (text ", ") (map pp ps)))
  pp (p :=>: q)     = pp p <+> text "=>" <+> pp q
  pp (Forall xs p)  = cat [ text "∀" <+> hcat (punctuate (text ", ") (map pp xs)) <> text "."
                          , pp p
                          ]
  pp (Exists xs p)  = cat [ text "∃" <+> hcat (punctuate (text ", ") (map pp xs)) <> text "."
                          , pp p
                          ]
  pp (Here e)       = text "here" <> parens (pp e)
  pp (NonDetProp)   = text "*"
  pp (PVar i)       = text i
  pp (Prop e)       = pp e
  pp (Let bs p)     = case bs of
                    [] -> pp p
                    _  -> text "let" <+>
                          (cat $ punctuate (text ", ") ((\(b,e) -> pp b <+> text "=" <+> pp e) <$> bs)) <+>
                          text "in" <+>
                          pp p

instance Pretty Rel where
  pp Eq     = equals
  pp Le     = text "≤"
  pp Lt     = text "<"
  pp Gt     = text ">"
  pp SetMem = text "∈"

instance Pretty (Expr a) where
  pp (Const i)        = int i
  pp (EmptySet)       = text "{}"
  pp (NonDetValue)    = text "*"
  pp (Var x)          = text x
  pp (Select e1 e2)   = pp e1 <> brackets (pp e2)
  pp (Store e1 e2 e3) = pp e1 <> brackets (pp e2 <+> text ":=" <+> pp e3)
  pp (Bin o e1 e2)    = pp e1 <+> pp o <+> pp e2
  pp (Ite p e1 e2)    = pp p <+> text "?" <+> pp e1 <+> text ":" <+> pp e2
  pp (PExpr p)        = text "Prop" <> parens (pp p)
  pp (Size e)         = text "|" <> pp e <> text "|"

instance Pretty Op where
  pp Plus         = text "+"
  pp Minus        = text "-"
  pp SetSubSingle = text "\\"
  pp SetAdd       = text "++"
  pp Mul          = text "*"
  pp Div          = text "/"

instance Pretty Binder where
  pp (Bind x t) = text x <> colon <> pp t

instance Pretty Sort where
  pp Int       = text "int"
  pp Set       = text "set"
  pp Bool      = text "bool"
  pp (Map i t) = pp i <+> text "->" <+> pp t

instance Pretty Index where
  pp (SetIdx i) = text i
  pp IntIdx     = text "int"
