package icetTerm

import (
	"fmt"
	"strings"
)

const PROC_SIZE = 5
const STMT_SIZE = 20
const SKIP = "skip"
const ANNOT_SIZE = 5

type IDType int

type AnnotatationType int

const ( // annotation types
	Inv     AnnotatationType = iota
	Prop                     = iota // property
	Pre                      = iota // precondition
	Assume                   = iota // assumtpion
	Declare                  = iota
	None                     = iota
)

const (
	Pid      IDType = iota
	Variable        = iota
)

type IcetTerm interface {
	PrintIceT(int) string
	PrettyPrint() string
}

// Programs
type Program struct {
	procs []IcetTerm
}

type Process struct {
	stmts []IcetTerm
}

type Declarations struct {
	Decls []string
}

type Assign struct {
	ProcID string
	Var    string
	Key    string
	Value  string
	IsMap  bool
}

type Send struct {
	ProcID        string
	RecipientID   string
	Value         string
	RecipientType IDType
}

type Recv struct {
	ProcID     string
	Variable   string
	FromId     string
	Decls      Declarations
	IsRecvFrom bool
}

type ForLoop struct {
	ProcID    string
	LoopVar   string
	Set       string
	Invariant string
	Stmts     Process
}

type RepeatLoop struct {
	ProcID string
	Stmts  Process
}

type SymSet struct {
	ProcVar string
	Name    string
	Stmts   Process
}

type Conditional struct {
	ProcID string
	Cond   string
	Left   Process
	Right  Process
}

type Annotation struct {
	Annot  string
	Type   AnnotatationType
	ProcID string
}

type AnnotationSet struct {
	Annots []Annotation
}

func indentationAtLv(lv int) string {
	ident := ""
	for i := 0; i < lv; i++ {
		ident = fmt.Sprintf("\t%v", ident)
	}
	return ident
}

// Declarations
func (c *Conditional) PrettyPrint() string {
	return fmt.Sprintf("%v: if %v then %v else %v\n", c.ProcID, c.Cond, c.Left.PrettyPrint(), c.Right.PrettyPrint())
}

func (c *Conditional) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	return fmt.Sprintf("%vite(%v,%v,\n%v,\n%v)", ident, c.ProcID, c.Cond, c.Left.PrintIceT(lv+1), c.Right.PrintIceT(lv+1))
}

func (d *Declarations) PrettyPrint() string {
	return fmt.Sprintf("declarations: %v\n", strings.Join(d.Decls, ","))
}

func MapToIcetTerm(vs []IcetTerm, lv int) []string {
	vsm := make([]string, len(vs))
	for i, v := range vs {
		vsm[i] = v.PrintIceT(lv)
	}
	return vsm
}

func joinWithIndent(strings []string, sep string, lv int) string {
	var ret string
	ident := indentationAtLv(lv)
	switch len(strings) {
	case 0:
		return ""
	case 1:
		return fmt.Sprintf("%v%v", ident, strings[0])
	}
	ret = ""
	for _, s := range strings[0 : len(strings)-1] {
		ret = fmt.Sprintf("%v%v%v%v", ret, ident, s, sep)
	}
	return fmt.Sprintf("%v%v%v", ret, ident, strings[len(strings)-1])
}

func (d *Declarations) PrintIceT(lv int) string {
	return fmt.Sprintf("[%v]", joinWithIndent(d.Decls, ",\n", lv))
}

func NewDeclarations() Declarations {
	return Declarations{make([]string, 0)}
}

func (d *Declarations) AppendDecl(decl string) {
	d.Decls = append(d.Decls, decl)
}

func (d *Declarations) Append(d1 *Declarations) {
	d.Decls = append(d.Decls, d1.Decls...)
}

// Assign statements
func (a *Assign) PrettyPrint() string {
	if a.IsMap {
		return fmt.Sprintf("%v: %v[%v]:=%v", a.ProcID, a.Var, a.Key, a.Value)
	}
	return fmt.Sprintf("%v: %v:=%v", a.ProcID, a.Var, a.Value)
}

func (a *Assign) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	if a.IsMap {
		return fmt.Sprintf("%vassign(%v,%v,upd(%v,%v,%v))", ident, a.ProcID, a.Var, a.Var, a.Key, a.Value)
	}
	return fmt.Sprintf("%vassign(%v,%v,%v)", ident, a.ProcID, a.Var, a.Value)
}

// Send statements
func (s *Send) PrettyPrint() string {
	return fmt.Sprintf("%v: send(%v, %v)", s.ProcID, s.RecipientID, s.Value)
}

func (s *Send) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	if s.RecipientType == Pid {
		return fmt.Sprintf("%vsend(%v, e_pid(%v), %v)", ident, s.ProcID, s.RecipientID, s.Value)
	}
	return fmt.Sprintf("%vsend(%v, e_var(%v), %v)", ident, s.ProcID, s.RecipientID, s.Value)
}

// Receive statements
func (r *Recv) PrettyPrint() string {
	if r.IsRecvFrom {
		return fmt.Sprintf("%v: %v:=recvFrom(%v)", r.ProcID, r.Variable, r.FromId)
	}
	return fmt.Sprintf("%v: recv(%v)", r.ProcID, r.Variable)
}

func (r *Recv) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	if r.IsRecvFrom {
		return fmt.Sprintf("%vrecv(%v, e_pid(%v), %v)", ident, r.ProcID, r.FromId, r.Variable)
	}
	return fmt.Sprintf("%vrecv(%v, %v)", ident, r.ProcID, r.Variable)
}

// For Loops

func (l *ForLoop) PrettyPrint() string {
	return fmt.Sprintf("%v: for %v in %v do %v end", l.ProcID, l.LoopVar, l.Set, l.Stmts.PrettyPrint())
}

func (l *ForLoop) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	if l.Invariant == "" {
		return fmt.Sprintf("%vfor(%v, %v, %v,\n %v)", ident, l.ProcID, l.LoopVar, l.Set, l.Stmts.PrintIceT(lv+1))
	}
	return fmt.Sprintf("%vfor(%v, %v, %v, rr, %v,\n %v)", ident, l.ProcID, l.LoopVar, l.Set, l.Invariant, l.Stmts.PrintIceT(lv+1))
}

// Repeat Loops
func (l *RepeatLoop) PrettyPrint() string {

	return fmt.Sprintf("%v: repeat %v end", l.ProcID, l.Stmts.PrettyPrint())
}

func (l *RepeatLoop) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	return fmt.Sprintf("%vwhile(%v, true,\n %v)\n", ident, l.ProcID, l.Stmts.PrintIceT(lv+1))
}

// Sets
func (s *SymSet) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	return fmt.Sprintf("%vsym(%v, %v,\n%v)", ident, s.ProcVar, s.Name, s.Stmts.PrintIceT(lv+1))
}

func (s *SymSet) PrettyPrint() string {
	return fmt.Sprintf("%v∏_%v:%v(\n%v)\n", s.ProcVar, s.Name, s.Stmts.PrettyPrint())
}

// Programs
func NewProgram() *Program {
	return &Program{make([]IcetTerm, 0, PROC_SIZE)}
}

func (p *Program) AddProc(proc IcetTerm) {
	p.procs = append(p.procs, proc)
}

func (p *Program) RemoveLastProc() (IcetTerm, bool) {
	if len(p.procs) > 0 {
		proc := p.procs[len(p.procs)-1]
		p.procs = p.procs[:len(p.procs)-1]
		return proc, true
	}
	return NewProcess(), false
}

func (p *Program) PrettyPrint() string {
	var prog string
	if len(p.procs) > 0 {
		prog = p.procs[0].PrettyPrint()
		for _, proccess := range p.procs[1:] {
			this := proccess.PrettyPrint()
			prog = fmt.Sprintf("%v || %v", prog, this)
		}
	} else {
		prog = SKIP
	}
	return prog
}

func (p *Program) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	switch len(p.procs) {
	case 0:
		return fmt.Sprintf("%v%v", ident, SKIP)
	case 1:
		return fmt.Sprintf("%v%v", ident, p.procs[0].PrintIceT(0))
	}
	strs := MapToIcetTerm(p.procs, lv+1)
	procs := joinWithIndent(strs, ",\n", 0)
	return fmt.Sprintf("%vpar([\n%v])", ident, procs)
	/*
		var prog string
		ident := indentationAtLv(lv)
		if len(p.procs) > 0 {
			prog = fmt.Sprintf("%vpar([\n%v", p.procs[0].PrintIceT(lv+1), ident)
			for _, proccess := range p.procs[1:] {
				this := proccess.PrintIceT(lv + 1)
				prog = fmt.Sprintf("%v,%v", prog, this)
			}
			prog = fmt.Sprintf("%v])", prog)
		} else {
			prog = fmt.Sprintf("%v%v", ident, SKIP)
		}
		return prog
	*/
}

// Processes
func NewProcess() *Process {
	return &Process{make([]IcetTerm, 0, STMT_SIZE)}
}

func (proc *Process) Len() int {
	return len(proc.stmts)
}

func (proc *Process) IsEmpty() bool {
	return len(proc.stmts) == 0
}

func (proc *Process) AddStmt(stmt IcetTerm) {
	proc.stmts = append(proc.stmts, stmt)
}

func (proc *Process) AddStmts(stmt []IcetTerm) {
	proc.stmts = append(proc.stmts, stmt...)
}

func (proc *Process) AddProc(proc1 *Process) {
	proc.stmts = append(proc.stmts, proc1.stmts...)
}

func (proc *Process) PrettyPrint() string {
	var stmts string
	if len(proc.stmts) > 0 {
		stmts = proc.stmts[0].PrettyPrint()
		for _, stmt := range proc.stmts[1:] {
			stmts = fmt.Sprintf("%v;%v", stmts, stmt.PrettyPrint())
		}
	} else {
		stmts = SKIP
	}
	return stmts
}

func (proc *Process) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	switch len(proc.stmts) {
	case 0:
		return fmt.Sprintf("%v%v", ident, SKIP)
	case 1:
		return fmt.Sprintf("%v%v", ident, proc.stmts[0].PrintIceT(0))
	}
	strs := MapToIcetTerm(proc.stmts, lv+1)
	procs := joinWithIndent(strs, ",\n", 0)
	return fmt.Sprintf("%vseq([\n%v\n%v])", ident, procs, ident)
}

// Annotations

func (a *Annotation) PrettyPrint() string {
	switch a.Type {
	case Pre:
		return fmt.Sprintf("precondition: %v", a.Annot)
	case Assume:
		return fmt.Sprintf("assumption: %v", a.Annot)
	}
	return ""
}

func (a *Annotation) PrintIceT(lv int) string {
	ident := indentationAtLv(lv)
	switch a.Type {
	case Pre:
		return fmt.Sprintf("%vpre(%v, %v)", ident, a.ProcID, a.Annot)
	case Assume:
		return fmt.Sprintf("%vassume(%v, %v)", ident, a.ProcID, a.Annot)
	case Prop:
		return fmt.Sprintf("%v%v", ident, a.Annot)
	}
	return ""
}

func (as *AnnotationSet) PrettyPrint() string {
	var s []string
	for _, a := range as.Annots {
		s = append(s, a.PrettyPrint())
	}
	return strings.Join(s, ",")
}

func (as *AnnotationSet) PrintIceT(lv int) string {
	if len(as.Annots) > 0 {
		ident := indentationAtLv(lv)
		var s []string
		for _, a := range as.Annots {
			s = append(s, a.PrintIceT(lv))
		}
		return fmt.Sprintf("%v%v", ident, strings.Join(s, ","))
	}
	return ""
}

func NewAnnotationSet() *AnnotationSet {
	return &AnnotationSet{Annots: make([]Annotation, 0)}
}

func (as *AnnotationSet) Add(a ...Annotation) {
	as.Annots = append(as.Annots, a...)
}
