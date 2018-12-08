// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.parser;

import java.io.PrintWriter;
import java.io.StringWriter;

import de.uka.ilkd.key.logic.op.SortDependingFunction;
import de.uka.ilkd.key.logic.sort.*;
import junit.framework.TestCase;

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.logic.sort.ParametricSort;
import static de.uka.ilkd.key.logic.sort.ParametricSort.Variance.*;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import org.key_project.util.collection.Immutables;


public class TestDeclParser extends TestCase {

    NamespaceSet nss;
    Services serv;
    private Namespace<SchemaVariable> parsedSchemaVars;

    public TestDeclParser(String name) {
	super(name);
    }

    public void setUp() {
	serv = new Services(AbstractProfile.getDefaultProfile());
	nss = serv.getNamespaces();
	
	String sorts = "\\sorts{boolean;int;LocSet;}";
	KeYParserF basicSortsParser = new KeYParserF(ParserMode.DECLARATION,
		new KeYLexerF(sorts,
			"No file. Call of parser from logic/TestClashFreeSubst.java"),
		serv, nss);
	try {
	    basicSortsParser.parseSorts();
	} catch(Exception e) {
	    throw new RuntimeException(e);
	}	
	
	Recoder2KeY r2k = new Recoder2KeY(serv, nss);
	r2k.parseSpecialClasses();
    }

    private KeYParserF stringParser(String s) {
	return new KeYParserF(ParserMode.DECLARATION,
		new KeYLexerF(s,
			"No file. Call of parser from parser/TestDeclParser.java"),
		serv, nss);
    }

    private void parseDecls(String s) {
	try {
	    KeYParserF p = stringParser(s);
	    p.decls();
	    this.parsedSchemaVars = p.schemaVariables();
	} catch (Exception e) {
	    StringWriter sw = new StringWriter();
	    PrintWriter pw = new PrintWriter(sw);
	    e.printStackTrace(pw);
	    throw new RuntimeException("Exc while Parsing:\n" + sw );
	}
    }

    public void testSortDecl() {


	parseDecls("\\sorts { elem; list; }");
	assertEquals("find sort elem", new Name("elem"),
		     nss.sorts().lookup(new Name("elem")).name()); 
	assertEquals("find sort list", new Name("list"),
		     nss.sorts().lookup(new Name("list")).name());
    }

	public void testSortDeclFail() {
		try {
			String s = "\\sorts { X; X; }";
			KeYParserF p = stringParser(s);
			p.decls();
			fail("Parsing " + s + " should have failed");
		} catch (Exception ex) {
			assertTrue(ex.getMessage().contains("already declared"));
		}

	}

	public void testParametericSortDecl() {
		parseDecls("\\sorts { \\generic E, F, G; " +
				"coll<[E]>; list<[+E]> \\extends coll<[E]>;" +
				"var<[-E, +F, G]>; }");

		Sort e = nss.sorts().lookup("E");
		ParametricSort list = (ParametricSort) nss.sorts().lookup("list");
		ParametricSort coll = (ParametricSort) nss.sorts().lookup("coll");
		ParametricSort var = (ParametricSort) nss.sorts().lookup("var");

		assertTrue(e instanceof GenericSort);
		assertTrue(coll instanceof ParametricSort);
		assertTrue(list instanceof ParametricSort);

		assertEquals(
				Immutables.listOf(CONTRAVARIANT, COVARIANT, INVARIANT),
				var.getCovariances());

		assertEquals("{coll<[E]>}", list.extendsSorts().toString());

		assertEquals("{any}", coll.extendsSorts().toString());
	}

	public void testParametericSortDeclFails() {
    	try {
			String s = "\\sorts { parametric<[E]>; }";
			KeYParserF p = stringParser(s);
			p.decls();
			fail("Parsing " + s + " should have failed");
		} catch (Exception ex) {
			assertTrue(ex.getMessage().contains("Formal type parameters must be (already declared) generic sorts"));
		}

		try {
			String s = "\\sorts { \\generic E; doubled<[E,E]>; }";
			KeYParserF p = stringParser(s);
			p.decls();
			fail("Parsing " + s + " should have failed");
		} catch (Exception ex) {
			assertTrue(ex.getMessage().contains("unique"));
		}


		try {
			String s = "\\sorts { parametric<[int]>; }";
			KeYParserF p = stringParser(s);
			p.decls();
			fail("Parsing " + s + " should have failed");
		} catch (Exception ex) {
			assertTrue(ex.getMessage().contains("Formal type parameters must be (already declared) generic sorts"));
		}

		try {
			String s = "\\sorts { \\generic E; int<[E]>; }";
			KeYParserF p = stringParser(s);
			p.decls();
			fail("Parsing " + s + " should have failed");
		} catch (Exception ex) {
			assertTrue(ex.getMessage().contains("already declared"));
		}
	}


    protected GenericSort checkGenericSort ( Named            p_n,
					     ImmutableSet<Sort>        p_ext,
					     ImmutableSet<Sort>        p_oneof ) {
	assertTrue ( "Generic sort does not exist", p_n != null );
	assertTrue ( "Generic sort does not have type GenericSort, but " + p_n.getClass(),
		     p_n instanceof GenericSort );

	GenericSort gs = (GenericSort)p_n;
	
	assertEquals ( "Generic sort has wrong supersorts",
		       p_ext,
		       gs.extendsSorts () );
	assertEquals ( "Generic sort has wrong oneof-list",
		       p_oneof,
		       gs.getOneOf () );
	
	return gs;
    }

    protected Sort checkSort ( Named p_n ) {
	assertTrue ( "Sort does not exist", p_n != null );
	assertTrue ( "Sort does not have type Sort, but " + p_n.getClass(),
		     p_n instanceof Sort );

	return (Sort)p_n;
    }

    public void testProxySortDecl() {
        nss = new NamespaceSet ();
        parseDecls("\\sorts { A; B; \\proxy P; \\proxy Q \\extends A,B; \\proxy R \\extends Q; }");

        Sort P = (Sort) nss.sorts().lookup(new Name("P"));
        assertTrue(P instanceof ProxySort);
        assertEquals("P", P.name().toString());
        assertEquals(DefaultImmutableSet.nil().add(Sort.ANY), P.extendsSorts());

        Sort A = (Sort) nss.sorts().lookup(new Name("A"));
        Sort B = (Sort) nss.sorts().lookup(new Name("B"));
        Sort Q = (Sort) nss.sorts().lookup(new Name("Q"));
        assertTrue(Q instanceof ProxySort);
        assertEquals("Q", Q.name().toString());
        assertEquals(DefaultImmutableSet.nil().add(A).add(B), Q.extendsSorts());

        Sort R = (Sort) nss.sorts().lookup(new Name("R"));
        assertTrue(P instanceof ProxySort);
        assertEquals("R", R.name().toString());
        assertEquals(DefaultImmutableSet.nil().add(Q), R.extendsSorts());
    }


    public void testGenericSortDecl() {
	GenericSort G, H;
	Sort        S, T;
	
	nss = new NamespaceSet ();
	parseDecls("\\sorts { \\generic G; \\generic H \\extends G; }");

	G = checkGenericSort ( nss.sorts().lookup(new Name("G")),
			       DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
			       DefaultImmutableSet.<Sort>nil() );
	H = checkGenericSort ( nss.sorts().lookup(new Name("H")),
			       DefaultImmutableSet.<Sort>nil().add ( G ),
			       DefaultImmutableSet.<Sort>nil() );


	nss = new NamespaceSet ();
	parseDecls("\\sorts { S; \\generic G; \\generic H \\extends G, S; }");
	
	S = checkSort        ( nss.sorts().lookup(new Name("S")) );
	G = checkGenericSort ( nss.sorts().lookup(new Name("G")),
			       DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
			       DefaultImmutableSet.<Sort>nil() );
	H = checkGenericSort ( nss.sorts().lookup(new Name("H")),
			       DefaultImmutableSet.<Sort>nil().add ( S ).add ( G ),
			       DefaultImmutableSet.<Sort>nil() );


	nss = new NamespaceSet ();
	parseDecls("\\sorts { S; T; \\generic H \\oneof {S, T}; }");

	S = checkSort        ( nss.sorts().lookup(new Name("S")) );
	T = checkSort        ( nss.sorts().lookup(new Name("T")) );
	H = checkGenericSort ( nss.sorts().lookup(new Name("H")),
			       DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
			       DefaultImmutableSet.<Sort>nil().add ( S ).add ( T ) );
	

	nss = new NamespaceSet ();
	parseDecls("\\sorts { S; T; \\generic G; \\generic H \\oneof {S} \\extends T, G; }");

	S = checkSort        ( nss.sorts().lookup(new Name("S")) );
	T = checkSort        ( nss.sorts().lookup(new Name("T")) );
	G = checkGenericSort ( nss.sorts().lookup(new Name("G")),
			       DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
			       DefaultImmutableSet.<Sort>nil() );
	H = checkGenericSort ( nss.sorts().lookup(new Name("H")),
			       DefaultImmutableSet.<Sort>nil().add ( T ).add ( G ),
			       DefaultImmutableSet.<Sort>nil().add ( S ) );
	

	nss = new NamespaceSet ();
	parseDecls("\\sorts { S, T; \\generic G,G2; \\generic H,H2 \\oneof {S} \\extends T, G; }");

	S = checkSort        ( nss.sorts().lookup(new Name("S")) );
	T = checkSort        ( nss.sorts().lookup(new Name("T")) );
	G = checkGenericSort ( nss.sorts().lookup(new Name("G")),
			       DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
			       DefaultImmutableSet.<Sort>nil() );
	checkGenericSort     ( nss.sorts().lookup(new Name("G2")),
			       DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
			       DefaultImmutableSet.<Sort>nil() );
	H = checkGenericSort ( nss.sorts().lookup(new Name("H")),
			       DefaultImmutableSet.<Sort>nil().add ( T ).add ( G ),
			       DefaultImmutableSet.<Sort>nil().add ( S ) );
	checkGenericSort     ( nss.sorts().lookup(new Name("H2")),
			       DefaultImmutableSet.<Sort>nil().add ( T ).add ( G ),
			       DefaultImmutableSet.<Sort>nil().add ( S ) );
	

	nss = new NamespaceSet ();
	String str = "\\sorts { \\generic G; \\generic H \\oneof {G}; }";
	try {
	    KeYParserF p = stringParser(str);
	    p.decls();

	    fail ( "Expected an GenericSortException" );
	} catch ( Exception e ) {
	    assertTrue ( "Expected a GenericSortException",
			 e instanceof de.uka.ilkd.key.parser.GenericSortException ||  e.getCause() instanceof de.uka.ilkd.key.parser.GenericSortException);
	}
    }

    /** asserts that the found object is a schemavariable and 
     * that the allowed macthing type is QuantifiableVariable
     */
    public void assertVariableSV(String msg, 
				 Object o) {
	assertTrue("The named object: "+o+" is of type "+o.getClass()+
		   ", but the type SchemaVariable was expected",
		   o instanceof SchemaVariable);

	assertTrue(msg, o instanceof VariableSV);
    }

    /** asserts that the SchemaVariable matches to term but not to a
     * formula 
     */
    public void assertTermSV(String msg, 
			     Object o) {

	assertTrue("The named object: "+o+" is of type "+o.getClass()+
		   ", but the type SchemaVariable was expected",
		   o instanceof SchemaVariable);
	assertTrue("Schemavariable is not allowed to match a term of sort FORMULA.",
		   ((SchemaVariable)o).sort() != Sort.FORMULA);
    }

    /** asserts that the SchemaVariable matches to a formula 
     * and not to a term (of sort != Sort.FORMULA)
     */
    public void assertFormulaSV(String msg, 
				Object o) {
	assertTrue("The named object: "+o+" is of type "+o.getClass()+
		   ", but the type SchemaVariable was expected",
		   o instanceof SchemaVariable);
	assertSame("Only matches to terms of sort FORMULA allowed. "+
		   "But term has sort "+((SchemaVariable)o).sort(), 
		   ((SchemaVariable)o).sort(), Sort.FORMULA);

	
    }
  
    public void testArrayDecl() {
	parseDecls("\\sorts { aSort;}\n" +
		   "\\functions {\n" +
		   "  aSort[][] f(aSort);\n" +
		   "}\n");
	Sort aSort = nss.sorts().lookup(new Name("aSort"));
	Sort objectSort = serv.getJavaInfo().objectSort();
	Sort cloneableSort = serv.getJavaInfo().cloneableSort();
        Sort serializableSort = serv.getJavaInfo().serializableSort();
	Sort aSortArr = ArraySort.getArraySort(aSort, objectSort, cloneableSort, serializableSort);
	Sort aSortArr2 = ArraySort.getArraySort(aSortArr, objectSort, cloneableSort, serializableSort);
	assertTrue("aSort[] should extend Cloneable: " + aSortArr.extendsSorts(), 
		   aSortArr.extendsSorts().contains(cloneableSort)); 
 	assertTrue("aSort[] should transitively extend Object ", 
		   aSortArr.extendsTrans(objectSort)); 
  	assertTrue("aSort[][] should transitively extend Object ", 
		   aSortArr2.extendsTrans(objectSort)); 
  	assertTrue("aSort[][] should transitively extend Cloneable ", 
		   aSortArr2.extendsTrans(cloneableSort));
	assertTrue("aSort[][] should extend Cloneable[] ", 
		   aSortArr2.extendsSorts().contains
		   (ArraySort.getArraySort(cloneableSort, objectSort, cloneableSort, serializableSort)));
  	assertTrue("Cloneable should extend Object ", 
		   cloneableSort.extendsSorts().contains(objectSort));
    }

    public void testFunctionPolymorphicDecl() {
		parseDecls("\\sorts { \\generic elem; list<[+elem]>; }\n" +
				"\\functions {\n" +
				"  elem elem::head(list<[elem]>);\n" +
				"  list<[elem]> elem::tail(list<[elem]>);\n" +
				"  list<[elem]> elem::nil;\n" +
				"  list<[elem]> elem::cons(elem, list<[elem]>);\n" +
				"}\n");


        SortDependingFunction head = (SortDependingFunction) nss.functions().lookup("any::head");
        SortDependingFunction inthead = head.getInstanceFor(nss.sorts().lookup("int"), serv);
        assertEquals("int", inthead.sort().toString());
        assertEquals("[list<[int]>]", inthead.argSorts().toString());

        SortDependingFunction cons = (SortDependingFunction) nss.functions().lookup("any::cons");
        SortDependingFunction intcons = cons.getInstanceFor(nss.sorts().lookup("int"), serv);
        assertEquals("list<[int]>", intcons.sort().toString());
        assertEquals("[int,list<[int]>]", intcons.argSorts().toString());

	}
  
    public void testFunctionDecl() {
	parseDecls("\\sorts { elem; list; }\n" +
		   "\\functions {\n" +
		   "  elem head(list);\n" +
		   "  list tail(list);\n" +
		   "  elem[] tailarray(elem[]);\n" +
		   "  list nil;\n" +
		   "  list cons(elem,list);\n" +
		   "}\n");
	
	Sort elem = nss.sorts().lookup(new Name("elem"));
	Sort list = nss.sorts().lookup(new Name("list"));

        Sort objectSort = serv.getJavaInfo().objectSort();
        Sort cloneableSort = serv.getJavaInfo().cloneableSort();
        Sort serializableSort = serv.getJavaInfo().serializableSort();
        
	assertEquals("find head function", new Name("head"),
		     nss.functions().lookup(new Name("head")).name());
	assertEquals("head arity", 1,
		     ((Function)nss.functions().lookup(new Name("head"))).arity());
	assertEquals("head arg sort 0", list,
		     ((Function)nss.functions().lookup(new Name("head"))).argSort(0));
	assertEquals("head return sort", elem,
		     ((Function)nss.functions().lookup(new Name("head"))).sort());

	assertEquals("find tail function", new Name("tail"),
		     nss.functions().lookup(new Name("tail")).name());
	assertEquals("tail arity", 1,
		     ((Function)nss.functions().lookup(new Name("tail"))).arity());
	assertEquals("tail arg sort 0", list,
		     ((Function)nss.functions().lookup(new Name("tail"))).argSort(0));
	assertEquals("tail return sort", list,
		     ((Function)nss.functions().lookup(new Name("tail"))).sort());
	assertEquals("tailarray arg sort 0", 
                ArraySort.getArraySort(elem, objectSort, cloneableSort, serializableSort),

		     ((Function)nss.functions().lookup(new Name("tailarray"))).argSort(0));
	assertEquals("tailarray return sort", ArraySort.getArraySort(elem, 
                objectSort, cloneableSort, serializableSort),
		     ((Function)nss.functions().lookup(new Name("tailarray"))).sort());

	assertEquals("find nil function", new Name("nil"),
		     nss.functions().lookup(new Name("nil")).name());
	assertEquals("nil arity", 0,
		     ((Function)nss.functions().lookup(new Name("nil"))).arity());
	assertEquals("nil return sort", list,
		     ((Function)nss.functions().lookup(new Name("nil"))).sort());

	assertEquals("find cons function", new Name("cons"),
		     nss.functions().lookup(new Name("cons")).name());
	assertEquals("cons arity", 2,
		     ((Function)nss.functions().lookup(new Name("cons"))).arity());
 	assertEquals("cons arg sort 0", elem,
		     ((Function)nss.functions().lookup(new Name("cons"))).argSort(0));
 	assertEquals("cons arg sort 1", list,
		     ((Function)nss.functions().lookup(new Name("cons"))).argSort(1));
	assertEquals("cons return sort", list,
		     ((Function)nss.functions().lookup(new Name("cons"))).sort());
    }

    public void testPredicateDecl() {
	parseDecls("\\sorts { elem; list; }\n" +
		   "\\predicates {\n" +
		   "  isEmpty(list);\n" +
		   "  contains(list,elem);\n" +
		   "  maybe;\n" +
		   "}\n");
	
	Sort elem = nss.sorts().lookup(new Name("elem"));
	Sort list = nss.sorts().lookup(new Name("list"));


	assertEquals("find isEmpty predicate", new Name("isEmpty"),
		     nss.functions().lookup(new Name("isEmpty")).name());
	assertEquals("isEmpty arity", 1,
		     ((Function)nss.functions().lookup(new Name("isEmpty"))).arity());
	assertEquals("isEmpty arg sort 0", list,
		   ((Function)nss.functions().lookup(new Name("isEmpty"))).argSort(0));
	assertEquals("isEmpty return sort", Sort.FORMULA,
		     ((Function)nss.functions().lookup(new Name("isEmpty"))).sort());

	assertEquals("find contains predicate", new Name("contains"),
		     nss.functions().lookup(new Name("contains")).name());
	assertEquals("contains arity", 2,
		     ((Function)nss.functions().lookup(new Name("contains"))).arity());
	assertEquals("contains arg sort 0", list,
		   ((Function)nss.functions().lookup(new Name("contains"))).argSort(0));
	assertEquals("contains arg sort 1", elem,
		   ((Function)nss.functions().lookup(new Name("contains"))).argSort(1));
	assertEquals("contains return sort", Sort.FORMULA,
		     ((Function)nss.functions().lookup(new Name("contains"))).sort());

	assertEquals("find maybe predicate", new Name("maybe"),
		     nss.functions().lookup(new Name("maybe")).name());
	assertEquals("maybe arity", 0,
		     ((Function)nss.functions().lookup(new Name("maybe"))).arity());
	assertEquals("maybe return sort", Sort.FORMULA,
		     ((Function)nss.functions().lookup(new Name("maybe"))).sort());
    }

    public void testSVDecl() {
	parseDecls("\\sorts { elem; list; }\n" +
		   "\\schemaVariables {\n" +
		   "  \\program Statement #s ; \n"+
		   "  \\term elem x,y ;\n" +
		   "  \\variables list lv ;\n" +
		   "  \\formula b;\n" +
		   "}\n");
	
	
	Sort elem = nss.sorts().lookup(new Name("elem"));
	Sort list = nss.sorts().lookup(new Name("list"));

	Namespace<SchemaVariable> variables = parsedSchemaVars;

	assertEquals("find SV x", new Name("x"),
		     variables.lookup(new Name("x")).name());
	assertTermSV("SV x type", 
		     variables.lookup(new Name("x")));
	assertEquals("SV x sort", elem,
		     ((SchemaVariable)variables.lookup(new Name("x"))).sort());

	assertEquals("find SV ", new Name("y"),
		     variables.lookup(new Name("y")).name());
	assertTermSV("SV y type", 
		     variables.lookup(new Name("y")));
	assertEquals("SV y sort", elem,
		     ((SchemaVariable)variables.lookup(new Name("y"))).sort());

	assertEquals("find SV ", new Name("lv"),
		     variables.lookup(new Name("lv")).name());
	assertVariableSV("SV lv type", 
		     variables.lookup(new Name("lv")));
	assertEquals("SV lv sort", list,
		     ((SchemaVariable)variables.lookup(new Name("lv"))).sort());
	
	assertEquals("find SV ", new Name("b"),
		     variables.lookup(new Name("b")).name());
	assertFormulaSV("SV b type", 
		     variables.lookup(new Name("b")));
	assertEquals("SV b sort", Sort.FORMULA,
		     ((SchemaVariable)variables.lookup(new Name("b"))).sort());
    }
    

    public void testAmbigiousDecls() {
	try {
	    stringParser
		("\\sorts { elem; list; }\n" +
		 "\\functions {" + 
		 "elem x;"+
		 "elem fn;"+
		 "elem p;"    +
		 "}" +
		 "\\predicates {" + 
		 "fn(elem);"+
		 "y;"    +
		 "p;"    +
		 "}" +
		 "\\schemaVariables {\n" +
		 "  \\program Statement #s ; \n"+
		 "  \\term elem x,y ;\n" +
		 "  \\variables list lv ;\n" +
		 "  \\formula b;\n" +
		 "}\n").decls();
	  fail("Parsed in ambigious declaration");
	} catch(RuntimeException e){
	    if(!(e.getCause() instanceof AmbigiousDeclException)){
	        e.printStackTrace();
		fail("Unexpected excpetion. Testcase failed." +e);
	    }
	} catch(RecognitionException re) {
	    if(!(re instanceof AmbigiousDeclException)) {
	        re.printStackTrace();
	        fail("Unexpected recognition excpetion. Testcase failed." + re);
	    }
	} 
	
    }


    public void testHeurDecl() {
	parseDecls("\\heuristicsDecl { bool; shoot_foot; }");
	assertEquals("find heuristic bool", new Name("bool"),
		     nss.ruleSets().lookup(new Name("bool")).name()); 
	assertEquals("find heuristic shoot_foot", new Name("shoot_foot"),
		     nss.ruleSets().lookup(new Name("shoot_foot")).name());
    }
    

}