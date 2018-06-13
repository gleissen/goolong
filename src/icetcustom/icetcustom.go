package icetcustom

import (
	"go/ast"
	"icetTerm"
)

type CustomParser interface {
	ParseSend(string, []ast.Expr, string, icetTerm.IDType, func(ast.Node) string) (bool, icetTerm.IcetTerm)
	ParseReceive(string, []ast.Expr, string, string, bool, func(ast.Node) string) (bool, icetTerm.IcetTerm)
}

// default implementation
type DefaultParser struct{}

func (d *DefaultParser) ParseSend(string, []ast.Expr, string, icetTerm.IDType, func(ast.Node) string) (bool, icetTerm.IcetTerm) {
	return false, nil
}

func (d *DefaultParser) ParseReceive(string, []ast.Expr, string, string, bool, func(ast.Node) string) (bool, icetTerm.IcetTerm) {
	return false, nil
}
