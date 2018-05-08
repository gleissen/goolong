package icetTerm

import (
	"fmt"
	"strings"
)

const PROC_SIZE = 5
const STMT_SIZE = 20
const SKIP = "skip"

type IcetTerm interface {
	PrettyPrint() string
	PrintIceT() string
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
	Value  string
}

type Send struct {
	ProcID      string
	RecipientID string
	Value       string
}

type Recv struct {
	ProcID     string
	Variable   string
	FromId     string
	IsRecvFrom bool
}

type ForLoop struct {
	ProcID    string
	LoopVar   string
	Set       string
	Invariant string
	Stmts     Process
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

// Declarations

func (c *Conditional) PrettyPrint() string {
	return fmt.Sprintf("%v: if %v then %v else %v\n", c.ProcID, c.Cond, c.Left.PrettyPrint(), c.Right.PrettyPrint())
}

func (c *Conditional) PrintIceT() string {
	return fmt.Sprintf("ite(%v, %v, %v, %v)", c.ProcID, c.Cond, c.Left.PrintIceT(), c.Right.PrintIceT())
}

func (d *Declarations) PrettyPrint() string {
	return fmt.Sprintf("declarations: %v\n", strings.Join(d.Decls, ","))
}

func (d *Declarations) PrintIceT() string {
	return fmt.Sprintf("[%v]", strings.Join(d.Decls, ","))
}

func (d *Declarations) AppendDecl(decl string) {
	d.Decls = append(d.Decls, decl)
}

func (d *Declarations) Append(d1 *Declarations) {
	d.Decls = append(d.Decls, d1.Decls...)
}

// Assign statements
func (a *Assign) PrettyPrint() string {
	return fmt.Sprintf("%v: %v:=%v", a.ProcID, a.Var, a.Value)
}

func (a *Assign) PrintIceT() string {
	return fmt.Sprintf("assign(%v,%v,%v)", a.ProcID, a.Var, a.Value)
}

// Send statements
func (s *Send) PrettyPrint() string {
	return fmt.Sprintf("%v: send(%v, %v)", s.ProcID, s.RecipientID, s.Value)
}

func (s *Send) PrintIceT() string {
	return fmt.Sprintf("send(%v, e_pid(%v), %v)", s.ProcID, s.RecipientID, s.Value)
}

// Receive statements
func (r *Recv) PrettyPrint() string {
	if r.IsRecvFrom {
		return fmt.Sprintf("%v: %v:=recvFrom(%v)", r.ProcID, r.Variable, r.FromId)
	}
	return fmt.Sprintf("%v: recv(%v)", r.ProcID, r.Variable)
}

func (r *Recv) PrintIceT() string {
	if r.IsRecvFrom {
		return fmt.Sprintf("recv(%v, e_pid(%v), %v)", r.ProcID, r.FromId, r.Variable)
	}
	return fmt.Sprintf("recv(%v, %v)", r.ProcID, r.Variable)
}

// For Loops

func (l *ForLoop) PrettyPrint() string {
	return fmt.Sprintf("%v: for %v in %v do %v end", l.ProcID, l.LoopVar, l.Set, l.Stmts.PrettyPrint())
}

func (l *ForLoop) PrintIceT() string {
	return fmt.Sprintf("for(%v, %v, %v, rr, %v, %v)", l.ProcID, l.LoopVar, l.Set, l.Invariant, l.Stmts.PrintIceT())
}

func (s *SymSet) PrintIceT() string {
	return fmt.Sprintf("sym(%v, %v, %v)", s.ProcVar, s.Name, s.Stmts.PrintIceT())
}

func (s *SymSet) PrettyPrint() string {
	return fmt.Sprintf("∏_%v:%v(%v)", s.ProcVar, s.Name, s.Stmts.PrettyPrint())
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

func (p *Program) PrintIceT() string {
	var prog string
	if len(p.procs) > 0 {
		prog = fmt.Sprintf("par([%v", p.procs[0].PrintIceT())
		for _, proccess := range p.procs[1:] {
			this := proccess.PrintIceT()
			prog = fmt.Sprintf("%v,%v", prog, this)
		}
		prog = fmt.Sprintf("%v])", prog)
	} else {
		prog = SKIP
	}
	return prog
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

func (proc *Process) PrintIceT() string {
	var stmts string
	if len(proc.stmts) > 0 {
		stmts = fmt.Sprintf("seq([%v", proc.stmts[0].PrintIceT())
		for _, stmt := range proc.stmts[1:] {
			stmts = fmt.Sprintf("%v,%v", stmts, stmt.PrintIceT())
		}
		stmts = fmt.Sprintf("%v])", stmts)
	} else {
		stmts = SKIP
	}
	return stmts
}
