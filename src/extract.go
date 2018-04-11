package main

import "go/token"
import "go/parser"
import "go/ast"
import "fmt"
import "log"

func main() {
	parse_call_sites()
}

func parse_call_sites() {
	// parsing file
	fset := token.NewFileSet()
	node, err := parser.ParseFile(fset, "../tests/test.go", nil, parser.ParseComments)
	if err != nil {
		log.Fatal(err)
	}
	// extracting call sites
	ast.Inspect(node, func(n ast.Node) bool {
		// Find Call sites
		site, ok := n.(*ast.CallExpr)
		if ok {
			fmt.Print(parse_send(site))
			fmt.Print(parse_recv(site))
		}
		return true
	})
}

//fmt.Sprintf("at %v, %s", e.When, e.What)
func parse_send(site *ast.CallExpr) string {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		x := sel.X.(*ast.Ident)
		if sel.Sel.Name == "Send" && x.Name == "gochai" {
			arg1 := site.Args[0].(*ast.BasicLit).Value
			arg2 := site.Args[1].(*ast.BasicLit).Value
			return fmt.Sprintf("send(%v, %v)\n", arg1, arg2)
		} else {
			return ""
		}
	} else {
		return ""
	}
}

func parse_recv(site *ast.CallExpr) string {
	sel, ok := site.Fun.(*ast.SelectorExpr)
	if ok {
		x := sel.X.(*ast.Ident)
		if sel.Sel.Name == "Recv" && x.Name == "gochai" {
			arg1 := site.Args[0].(*ast.BasicLit).Value
			arg2 := site.Args[1].(*ast.BasicLit).Value
			return fmt.Sprintf("recv(%v, %v)\n", arg1, arg2)
		} else {
			return ""
		}
	} else {
		return ""
	}
}
