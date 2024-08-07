package main

import (
	"bufio"
	"fmt"
	"io"
	"log"
	"os"
	"strconv"
	"unicode"
)

const (
	Lambda int = iota
	LParen
	RParen
	Dot
	Equals
	Ident

	LamTerm
	IdxTerm
	VarTerm
	AppTerm
	LetTerm
)

var (
	environment map[string]Term = make(map[string]Term)
	indices     []string        = make([]string, 0)
	verbose                     = false
	natural                     = false

	prelude = []string{
		"I = λa.a",
		"M = λf.f f",
		"K = λa.λb.a",
		"KI = K I",
		"C = λf.λa.λb.f b a",
		"B = λf.λg.λa.f(g a)",
		"B1 = B B B",
		"Th = λa.λf.f a",
		"V = λa.λb.λf.f a b",
		"S = λa.λb.λc.a c (b c)",

		"T = K",
		"F = KI",
		"and = λa.λb.a b a",
		"or = λa.λb.a a b",
		"eq = λa.λb.a (b T F) (b F T)",
		"not = C",

		"pair = V",
		"fst = λp.p K",
		"snd = λp.p KI",
		"phi = λp.pair (snd p) (succ (snd p))",

		//"succ = λn.λf.B f (n f)",
		"succ = λn.λf.λx. f (n f x)",
		"pred = λn.fst (n phi (pair 0 0))",
		"plus = λa.λb.a succ b",
		"sub  = λn.λk.k pred n",
		"mult = B",
		"pow = Th",
		"is0 = λa.a (K F) T",
		"leq = λn.λk.is0 (sub n k)",
		"gt = B1 not leq",
		"eq_num = λn.λk.and (leq n k) (leq k n)",
		"lt = λa.λb.and(leq a b)((B1 not eq_num)a b)",
		"geq = B1 not lt",
	}
)

type Token struct {
	ttype int
	value string
}

type Parser struct {
	toks      []Token
	boundVars []string
}

type Term interface {
	etype() int
	printTerm(indent int)
	PPrint()
	equal(other Term) bool
	beta(idx uint, s Term) Term
}

type Abstraction struct {
	expr Term
}

type Var struct {
	name string
}

type Index struct {
	index uint
}

type Application struct {
	toCall Term
	arg    Term
}

type Let struct {
	name string
	expr Term
}

func newIndex(t string) {
	indices = append(indices, t)
}

func popIndex() {
	indices = indices[:len(indices)-1]
}

func getIndex(i uint) string {
	return indices[len(indices)-int(i)-1]
}

func (p *Parser) addBoundVar(v string) {
	p.boundVars = append(p.boundVars, v)
}

func (p *Parser) removeBoundVar() {
	p.boundVars = p.boundVars[:len(p.boundVars)-1]
}

func (p Parser) getIndex(v string) int {
	for i := len(p.boundVars); i > 0; i-- {
		if p.boundVars[i-1] == v {
			return len(p.boundVars) - i
		}
	}
	return -1
}

func (Abstraction) etype() int {
	return LamTerm
}

func (Index) etype() int {
	return IdxTerm
}

func (Var) etype() int {
	return VarTerm
}

func (Application) etype() int {
	return AppTerm
}

func (Let) etype() int {
	return LetTerm
}

func (f Abstraction) printTerm(indent int) {
	for i := 0; i < indent; i++ {
		fmt.Print("  ")
	}
	fmt.Print("FUNCTION - ")
	fmt.Print("\n")
	f.expr.printTerm(indent + 1)
}

func (f Abstraction) PPrint() {
	fmt.Print("\u03bb")
	//fmt.Print(f.arg)
	fmt.Print(".")
	f.expr.PPrint()
}

func (idx Index) printTerm(indent int) {
	for i := 0; i < indent; i++ {
		fmt.Print("  ")
	}
	fmt.Print("INDEX ")
	fmt.Print(idx)
	fmt.Print("\n")
}

func (i Index) PPrint() {
	fmt.Print(".")
	fmt.Print(i)
}

func (v Var) printTerm(indent int) {
	for i := 0; i < indent; i++ {
		fmt.Print("  ")
	}
	fmt.Print("VARIABLE ")
	fmt.Print(v.name)
	fmt.Print("\n")
}

func (v Var) PPrint() {
	fmt.Print(v.name)
}

func (c Application) printTerm(indent int) {
	for i := 0; i < indent; i++ {
		fmt.Print("  ")
	}
	fmt.Println("APPLICATION")
	c.toCall.printTerm(indent + 1)
	for i := 0; i < indent+1; i++ {
		fmt.Print("  ")
	}
	fmt.Println("With Argument")
	c.arg.printTerm(indent + 2)
}

func (c Application) PPrint() {
	fmt.Print("(")
	c.toCall.PPrint()
	fmt.Print(" ")
	c.arg.PPrint()
	fmt.Print(")")
}

func (a Let) printTerm(indent int) {
	for i := 0; i < indent; i++ {
		fmt.Print("  ")
	}
	fmt.Print("LET: ")
	fmt.Print(a.name)
	fmt.Print("\n")
	a.expr.printTerm(indent + 1)
}

func (Let) PPrint() {
	fmt.Print("")
}

func (a Abstraction) equal(other Term) bool {
	if other == nil {
		return false
	}
	if other.etype() != LamTerm {
		return false
	}
	return a.expr.equal(other.(*Abstraction).expr)
}

func (i Index) equal(other Term) bool {
	if other == nil {
		return false
	}
	if other.etype() != IdxTerm {
		return false
	}
	return i.index == other.(*Index).index
}

func (v Var) equal(other Term) bool {
	if other == nil {
		return false
	}
	if other.etype() != VarTerm {
		return false
	}
	otherV := other.(*Var)
	return v.name == otherV.name
}

func (a Application) equal(other Term) bool {
	if other == nil {
		return false
	}
	if other.etype() != AppTerm {
		return false
	}
	otherA := other.(*Application)
	return a.toCall.equal(otherA.toCall) &&
		a.arg.equal(otherA.arg)
}

func (Let) equal(other Term) bool {
	return false
}

func numToAbstraction(n uint64) Term {
	var expr Term
	expr = &Index{0}
	for i := uint64(0); i < n; i++ {
		expr = &Application{&Index{1}, expr}
	}
	return &Abstraction{&Abstraction{expr}}
}
func incIndices(idx uint, t Term) Term {
	switch t.etype() {
	case IdxTerm:
		i := t.(*Index).index
		if i >= idx {
			return &Index{i + 1}
		}
		return t
	case VarTerm:
		return t
	case LamTerm:
		return &Abstraction{incIndices(idx+1, t.(*Abstraction).expr)}
	case AppTerm:
		return &Application{incIndices(idx, t.(*Application).toCall),
			incIndices(idx, t.(*Application).arg)}
	case LetTerm:
		return t
	}
	return t
}

func (ab Abstraction) beta(idx uint, t Term) Term {
	return &Abstraction{ab.expr.beta(idx+1, incIndices(idx, t))}
}

func (i Index) beta(idx uint, t Term) Term {
	if i.index == idx {
		return t
	}
	if i.index > idx {
		return &Index{i.index - 1}
	}
	return &i
}

func (v Var) beta(idx uint, t Term) Term {
	return &v
}

func (ap Application) beta(idx uint, t Term) Term {
	return &Application{ap.toCall.beta(idx, t), ap.arg.beta(idx, t)}
}

func (a Let) beta(idx uint, t Term) Term {
	return &a
}

func isValueType(t Term) bool {
	switch t.etype() {
	case LamTerm:
		return true
	case IdxTerm:
		return true
	case VarTerm:
		_, ok := environment[t.(*Var).name]
		return !ok
	}
	return false
}

func norm(t Term) Term {
	switch t.etype() {
	case LetTerm:
		l := t.(*Let)
		environment[l.name] = norm(l.expr)
		return environment[l.name]
	case LamTerm:
		return &Abstraction{norm(t.(*Abstraction).expr)}
	case IdxTerm:
		return t
	case VarTerm:
		v := t.(*Var)
		val, ok := environment[v.name]
		if ok {
			return val
		}
		return v
	case AppTerm:
		ap := t.(*Application)
		var apOld *Application = ap
		for count := 0; count < 20000 && (count == 0 || !ap.equal(apOld)); count++ {
			apOld = ap
			var tNew Term
			if ap.toCall.etype() == LamTerm && isValueType(ap.arg) {
				if verbose {
					log.Println("norm lambda application")
				}
				tNew = ap.toCall.(*Abstraction).expr.beta(0, ap.arg)
			} else if ap.toCall.etype() == LamTerm {
				tNew = ap.toCall.(*Abstraction).expr.beta(0, norm(ap.arg))
			} else if isValueType(ap.toCall) {
				if verbose {
					log.Println("norm value application, toCall is")
					ap.toCall.printTerm(0)
				}
				tNew = &Application{ap.toCall, norm(ap.arg)}
			} else {
				if verbose {
					log.Println("norm non-value application, toCall is ")
					ap.toCall.printTerm(0)
				}
				tNew = &Application{norm(ap.toCall), ap.arg}
			}
			if tNew.etype() != AppTerm {
				return norm(tNew)
			}
			ap = tNew.(*Application)
		}
		return ap
	}
	return t
}

func PrintToken(tok Token) {
	switch tok.ttype {
	case Lambda:
		fmt.Print("\u03bb")
	case LParen:
		fmt.Print("LPAREN")
	case RParen:
		fmt.Print("RPAREN")
	case Dot:
		fmt.Print("DOT")
	case Equals:
		fmt.Print("EQUALS")
	case Ident:
		fmt.Print("[IDENT ")
		fmt.Print(tok.value)
		fmt.Print("]")
	}
}

func PrintTokens(toks []Token) {
	for i, tok := range toks {
		if i > 0 {
			fmt.Print(" ")
		}
		PrintToken(tok)
	}
	fmt.Println("")
}

func (parser *Parser) parseAtom() Term {
	if len(parser.toks) == 0 {
		return nil
	}
	if parser.toks[0].ttype == LParen {
		parser.skip(1)
		term := parser.parseTerm()
		// Should be at RParen now
		parser.skip(1)
		return term
	} else if parser.toks[0].ttype == Ident {
		idx := parser.getIndex(parser.toks[0].value)
		if idx < 0 {
			v := &Var{parser.toks[0].value}
			parser.skip(1)
			if natural {
				n, err := strconv.ParseUint(v.name, 10, 0)
				if err == nil {
					return numToAbstraction(n)
				}
			}
			return v
		}
		parser.skip(1)
		return &Index{uint(idx)}
	}
	return nil
}

func (parser *Parser) parseApplication() Term {
	if len(parser.toks) == 0 {
		return nil
	}
	lhs := parser.parseAtom()
	for {
		rhs := parser.parseAtom()
		if rhs == nil {
			return lhs
		}
		lhs = &Application{lhs, rhs}
	}
}

func (parser *Parser) parseTerm() Term {
	if len(parser.toks) == 0 {
		return nil
	}
	if parser.toks[0].ttype == Lambda && len(parser.toks) > 3 {
		arg := parser.toks[1].value
		parser.addBoundVar(arg)
		// Should have DOT now
		parser.skip(3)
		term := parser.parseTerm()
		parser.removeBoundVar()
		return &Abstraction{term}
	}
	return parser.parseApplication()
}

func (parser *Parser) parse() Term {
	if len(parser.toks) >= 2 && parser.toks[0].ttype == Ident &&
		parser.toks[1].ttype == Equals {
		to_bind := parser.toks[0].value
		parser.skip(2)
		expr := parser.parseTerm()
		return &Let{name: to_bind, expr: expr}
	}
	expr := parser.parseTerm()
	return expr
}

func (parser *Parser) skip(i int) {
	parser.toks = parser.toks[i:]
}

func lex(expr string) []Token {
	toks := make([]Token, 0)
	inIdent := false
	ident := make([]rune, 0)
	for _, c := range expr {
		if unicode.IsSpace(c) {
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			continue
		}
		switch c {
		case '(':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{LParen, string(c)})
		case ')':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{RParen, string(c)})
		case '.':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{Dot, string(c)})
		case '\\':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{Lambda, string(c)})
		case '\u03bb':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{Lambda, string(c)})
		case '=':
			if inIdent {
				toks = append(toks, Token{Ident, string(ident)})
				ident = nil
				inIdent = false
			}
			toks = append(toks, Token{Equals, string(c)})
		default:
			inIdent = true
			ident = append(ident, c)
		}
	}
	if inIdent {
		toks = append(toks, Token{Ident, string(ident)})
	}
	return toks
}

func isNatural(lam *Abstraction) bool {
	if lam.expr.etype() != LamTerm {
		return false
	}
	sec := lam.expr.(*Abstraction)
	if sec.expr.etype() == IdxTerm {
		return sec.expr.(*Index).index == 0
	}
	if sec.expr.etype() != AppTerm {
		//log.Println("Looking for natural, but not an application.")
		return false
	}

	app := sec.expr.(*Application)
	if app.toCall.etype() != IdxTerm || app.toCall.(*Index).index != 1 {
		return false
	}
	appP := app.arg
	if appP.etype() == AppTerm {
		app = appP.(*Application)
		for app.toCall.etype() == IdxTerm && app.toCall.(*Index).index == 1 &&
			app.arg.etype() == AppTerm {
			app = app.arg.(*Application)
		}
	}
	return app.toCall.etype() == IdxTerm && app.arg.etype() == IdxTerm
}

func toNatural(lam *Abstraction) int {
	expr := lam.expr.(*Abstraction).expr
	if expr.etype() == IdxTerm {
		return 0
	}
	app := expr.(*Application)
	ret := 1
	for app.arg.etype() == AppTerm {
		ret += 1
		app = app.arg.(*Application)
	}
	return ret
}

func repl() {
	for {
		reader := bufio.NewReader(os.Stdin)
		fmt.Print("> ")
		text, err := reader.ReadString('\n')
		if err != nil {
			if err != io.EOF {
				fmt.Println("Error")
			}
			break
		}
		if len(text) == 1 {
			continue
		}
		toks := lex(text)
		//PrintTokens(toks)
		parser := Parser{toks, make([]string, 0)}
		expr := parser.parse()
		if verbose {
			expr.printTerm(0)
		}
		f := norm(expr)
		if natural && f.etype() == LamTerm && isNatural(f.(*Abstraction)) {
			fmt.Print(toNatural(f.(*Abstraction)))
			fmt.Print(" (")
			f.PPrint()
			fmt.Print(")")
		} else if f.etype() == LamTerm {
			for n, e := range environment {
				//if f.equal(norm(e, 0)) {
				if f.equal(e) {
					fmt.Print(n, " ")
				}
			}
			fmt.Print("(")
			f.PPrint()
			fmt.Print(")")
		} else {
			f.PPrint()
		}
		fmt.Println("")
	}
}

func loadFile(name string) {
	file, err := os.Open(name)
	if err != nil {
		log.Fatal(err)
	}
	defer file.Close()

	scanner := bufio.NewScanner(file)
	for scanner.Scan() {
		if len(scanner.Text()) == 0 {
			continue
		}
		parser := Parser{lex(scanner.Text()), make([]string, 0)}
		expr := parser.parse()
		norm(expr)
	}

	if err := scanner.Err(); err != nil {
		log.Fatal(err)
	}
}

func main() {
	for args := os.Args[1:]; len(args) > 0; args = args[1:] {
		if args[0] == "--prelude" {
			for _, l := range prelude {
				parser := Parser{lex(l), make([]string, 0)}
				norm(parser.parse())
			}
			natural = true
		} else if args[0] == "--load" && len(args) > 1 {
			log.Println("Opening ", args[1])
			loadFile(args[1])
			args = args[1:]
		} else if args[0] == "--verbose" {
			verbose = true
		}
	}
	repl()
}
