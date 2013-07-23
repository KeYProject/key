// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.logic;

import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;
import java.util.Stack;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.LogicVariable;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.logic.op.Quantifier;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.parser.KeYLexer;
import de.uka.ilkd.key.parser.KeYParser;
import de.uka.ilkd.key.parser.ParserMode;
import de.uka.ilkd.key.proof.init.AbstractProfile;

public class TestClashFreeSubst extends TestCase {
 
    TermFactory tf=TermFactory.DEFAULT;

    Services services;
    NamespaceSet nss;

    Sort srt;

    Function f,g;
    Function p,q;

    LogicVariable v,x,y,z;
    Term t_v,t_x,t_y,t_z;

    ProgramVariable pv0;

    public TestClashFreeSubst(String name) {
	super(name);
    }

    public void setUp() {
	services = new Services(AbstractProfile.getDefaultProfile());
	nss = services.getNamespaces();
	
	String sorts = "\\sorts{boolean;int;LocSet;}";
	KeYParser basicSortsParser = new KeYParser(ParserMode.DECLARATION, new KeYLexer(new StringReader(sorts),null),
			      "No file. Call of parser from logic/TestClashFreeSubst.java",
			      services, nss);
	try {
	    basicSortsParser.parseSorts();
	} catch(Exception e) {
	    throw new RuntimeException(e);
	}
	
	Recoder2KeY r2k = new Recoder2KeY(services, nss);
	r2k.parseSpecialClasses();
	

	parseDecls("\\sorts { srt; }\n" +
		   "\\functions {\n" +
		   "  srt f(srt);\n" +
		   "  srt g(srt,srt);\n" +
		   "}\n" +
		   "\\predicates {\n" +
		   "  p(srt);\n" +
		   "  q(srt,srt);\n" +
		   "}"
		   );
	
	srt = lookup_sort("srt");


	f = lookup_func("f"); g = lookup_func("g");
	p = lookup_func("p"); q = lookup_func("q");
	pv0 = new LocationVariable (new ProgramElementName ( "pv0" ), srt);
	nss.variables().add ( pv0 );
	
	// The declaration parser cannot parse LogicVariables; these
	// are normally declared in quantifiers, so we introduce them
	// ourselves!
	v = declareVar("v",srt);   t_v = tf.createTerm(v);
	x = declareVar("x",srt);   t_x = tf.createTerm(x);
	y = declareVar("y",srt);   t_y = tf.createTerm(y);
	z = declareVar("z",srt);   t_z = tf.createTerm(z);
    }

    Sort lookup_sort(String name) {
	Sort s = (Sort)nss.sorts().lookup(new Name(name));
 	if ( s == null ) {
	    throw new RuntimeException("Sort named "+name+" not found");
	}
	return s;
    }
    
    Function lookup_func(String name) {
	Function f = (Function)nss.functions().lookup(new Name(name));
 	if ( f == null ) {
	    throw new RuntimeException("Function named "+name+" not found");
	}
	return f;
    }

    LogicVariable declareVar(String name,Sort sort) {
	LogicVariable v = new LogicVariable(new Name(name),sort);
	nss.variables().add(v);
	return v;
    }
    

    private KeYParser stringDeclParser(String s) {

	return new KeYParser(ParserMode.DECLARATION, new KeYLexer(new StringReader(s),null),
			      "No file. Call of parser from logic/TestClashFreeSubst.java",
			      services, nss);
    }

    public void parseDecls(String s) {
	try {
	    KeYParser p = stringDeclParser(s);
	    p.decls();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }

    private KeYParser stringTermParser(String s) {
	return new KeYParser(ParserMode.GLOBALDECL,
			     new KeYLexer(new StringReader(s),null),
			     services, 
			     nss);
    }

    public Term parseTerm(String s) {
	try {
	    KeYParser p = stringTermParser(s);
 	    return p.term();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }


    public Term parseFma(String s) {
	try {
	    KeYParser p = stringTermParser(s);
	    
	    return p.formula();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }


    /** transform sequences all x. all y. ... bla to  all x,y... . bla).
     * no rulevars, no javaBlocks.*/
    private Term toMulti(Term t) {
	ToMultiVisitor v = new ToMultiVisitor();
	t.execPostOrder(v);
	return v.getResult();
    }

    private class ToMultiVisitor extends DefaultVisitor {
	private Stack subStack;
	
	ToMultiVisitor() {
	    subStack = new Stack();
	}
	
	public void visit(Term visited) {
	    Operator op = visited.op();
	    int arity = visited.arity();
	    if ( op == Quantifier.ALL ) {
		Term top = (Term) subStack.peek();
		if ( top.op() == Quantifier.ALL )  {
		    QuantifiableVariable[] bv = 
			new QuantifiableVariable[visited.varsBoundHere(0).size()
						+top.varsBoundHere(0).size()];
		    for( int i = 0; i<visited.varsBoundHere(0).size(); i++ ) {
			bv[i] = visited.varsBoundHere(0)
			    .get(i);
		    }
		    for( int i = 0; i<top.varsBoundHere(0).size(); i++ ) {
			bv[visited.varsBoundHere(0).size()+i] = 
			    top.varsBoundHere(0).get(i);
		    }
		    subStack.pop();
		    subStack.push(TermBuilder.DF.all(ImmutableSLList.<QuantifiableVariable>nil().append(bv), top.sub(0)));
		    return;
		}
	    }
	    Term[] sub = new Term[arity];
	    for ( int i = arity-1; i>=0; i-- ) {
		sub[i] = (Term) (subStack.pop());
	    }
	    subStack.push(tf.createTerm(op, sub, visited.boundVars(), null));
	}

	Term getResult() {
	    return (Term) subStack.pop();
	}
    }

    // Test Cases

    public void testSubst() {
	Term s = parseTerm("f(x)");
	Term t = parseTerm("g(v,x)");
	ClashFreeSubst cfs = new ClashFreeSubst(v,s);
	assertEquals("substitution",
		     parseTerm("g(f(x),x)"),
		     cfs.apply(t));
    }

    public void testSubstWary() {
	Term s = parseTerm("f(x)");
	Term t = parseTerm("q(v,x)");
	WaryClashFreeSubst cfs = new WaryClashFreeSubst(v,s);
	assertEquals("substitution",
		     parseTerm("q(f(x),x)"),
		     cfs.apply(t));
    }

    public void testShare() {
	Term s = parseTerm("f(x)");
	Term t = parseTerm("g(v,f(x))");
	ClashFreeSubst cfs = new ClashFreeSubst(v,s);
	assertSame("share unchanged subterms", 
		   t.sub(1), cfs.apply(t).sub(1));
    }

    public void testShareWary() {
	Term s = parseTerm("f(x)");
	Term t = parseTerm("q(v,f(x))");
	WaryClashFreeSubst cfs = new WaryClashFreeSubst(v,s);
	assertSame("share unchanged subterms", 
		   t.sub(1), cfs.apply(t).sub(1));
    }

    /*
    public void testShareBound() {
	Term s = parseTerm("f(x)");
	Term t = parseTerm("g(v,eps v.q(x,v))");
	ClashFreeSubst cfs = new ClashFreeSubst(v,s);
	assertSame("sharing with bound variables", 
		   t.sub(1), cfs.apply(t).sub(1));
    }

    public void testShareAll() {
	Term s = parseTerm("f(x)");
	Term t = parseTerm("eps x.g(x,eps v.q(x,v))");
	ClashFreeSubst cfs = new ClashFreeSubst(v,s);
	assertSame("sharing whole term despite clash", 
		   t, cfs.apply(t));
    }
    */

    public void testClash() {
	Term s = parseTerm("f(x)");
	Term t = parseTerm("\\exists x; q(x,v)");
	ClashFreeSubst cfs = new ClashFreeSubst(v,s);
	Term res = cfs.apply(t);
	QuantifiableVariable x1 = 
	    res.varsBoundHere(0).get(0);
	nss.setVariables(new Namespace(nss.variables(), x1));
	assertEquals("clash resolution", 
		     parseTerm("\\exists x1; q(x1,f(x))"),
		     res);
	nss.setVariables(nss.variables().parent());
    }

    public void testSubstInSubstTerm() {
	Term s = parseTerm("f(x)");
	Term t = parseTerm("{\\subst y; f(v)}g(y,v)");
	ClashFreeSubst cfs = new ClashFreeSubst(v,s);
	assertEquals("substitute into substitution term",
		     parseTerm("{\\subst y; f(f(x))}g(y,f(x))"),
		     cfs.apply(t));
    }

    public void testClashInSubstTerm() {
	Term s = parseTerm("f(x)");
	Term t = parseTerm("{\\subst x; f(v)}g(x,v)");
	ClashFreeSubst cfs = new ClashFreeSubst(v,s);
	Term res = cfs.apply(t);
	QuantifiableVariable x1 = 
	    res.varsBoundHere(1).get(0);
	nss.setVariables(new Namespace(nss.variables(), x1));
	assertEquals("clash resolution in substitution term", 
		     parseTerm("{\\subst x1; f(f(x))}g(x1,f(x))"),
		     res);
	nss.setVariables(nss.variables().parent());
    }
    

    public void testMultiSubst() {
	Term s = parseTerm("f(x)");
	Term t = toMulti(parseFma("\\forall y; \\forall z; q(y,g(v,z))"));
	ClashFreeSubst cfs = new ClashFreeSubst(v,s);
	assertEquals("substitution on multi",
		     toMulti(parseFma("\\forall y; \\forall z; q(y,g(f(x),z))")),
		     cfs.apply(t));
    }

    public void testMultiShareBound() {
	Term s = parseTerm("f(x)");
	Term t = toMulti(parseFma("\\forall y; \\forall v; \\forall z; q(y,g(v,z))"));
	ClashFreeSubst cfs = new ClashFreeSubst(v,s);
	assertSame("sharing on multi",
		   cfs.apply(t), t);
    }

    // disabled. multi vars at quantifier currently not supported by
    // KeY and feature of data structures suppressed by TermFactory. /AR 040420
    public void xtestMultiClash() {
	Term s = parseTerm("f(x)");
	Term t = toMulti(parseFma("\\forall y; \\forall x; \\forall z; q(g(x,y),g(v,z))"));
	ClashFreeSubst cfs = new ClashFreeSubst(v,s);
	Term res = cfs.apply(t);
	QuantifiableVariable x1 = 
	    res.varsBoundHere(0).get(1);
	nss.setVariables(new Namespace(nss.variables(), x1));
	assertEquals("clash resolution in multi term", 
		     toMulti(parseTerm(
			       "\\forall y; \\forall x1; \\forall z; q(g(x1,y),g(f(x),z))")),
		     res);
	nss.setVariables(nss.variables().parent());
    }

    // disabled. multi vars at quantifier currently not supported by
    // KeY and feature of data structures suppressed by TermFactory. /AR 040420
    public void xtestMultiClash1() {
	Term s = parseTerm("f(x)");
	Term t = toMulti(parseFma("\\forall y; \\forall x;\\forall z; q(g(x,y),g(v,z))"));
	ClashFreeSubst cfs = new ClashFreeSubst(v,s);
	Term res = cfs.apply(t);
	QuantifiableVariable x1 = 
	    res.varsBoundHere(0).get(2);
	nss.setVariables(new Namespace(nss.variables(), x1));
	assertEquals("clash resolution in multi term", 
		     toMulti(parseTerm(
			       "q(g(x1,y),g(f(x),z))")),
		     res.sub(0));
	nss.setVariables(nss.variables().parent());
    }

    
    public void testWary0() {
	Term s = parseTerm("f(pv0)");
	Term t = parseTerm("q(v,x)");
	WaryClashFreeSubst cfs = new WaryClashFreeSubst(v,s);
	assertEquals("substitution",
		     parseTerm("q(f(pv0),x)"),
		     cfs.apply(t));
    }
    
    public void testWary1() {
	Term s = parseTerm("f(pv0)");
	Term t = parseTerm("q(v,x) & {pv0:=v}q(x,x)");
	WaryClashFreeSubst cfs = new WaryClashFreeSubst(v,s);
	assertEquals("substitution",
		     parseTerm("q(f(pv0),x) & {pv0:=f(pv0)}q(x,x)"),
		     cfs.apply(t));
    }
    
    public void testWary2() {
	Term s = parseTerm("f(pv0)");
	Term t = parseTerm("q(v,x) & {pv0:=v}q(x,v)");
	WaryClashFreeSubst cfs = new WaryClashFreeSubst(v,s);
	Term res = cfs.apply(t);
	QuantifiableVariable x1 = 
	    res.varsBoundHere(1).get(0);
	nss.setVariables(new Namespace(nss.variables(), x1));
	assertEquals("substitution",
		     parseTerm("{\\subst " + x1.name () +
			       "; f(pv0)} ( q(f(pv0),x) & {pv0:=f(pv0)}q(x," +
			       x1.name () + ") )"),
		     cfs.apply(t));
	nss.setVariables(nss.variables().parent());
    }
}
