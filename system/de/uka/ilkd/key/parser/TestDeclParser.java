// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.parser;

import java.io.PrintWriter;
import java.io.StringReader;
import java.io.StringWriter;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.SortedSchemaVariable;
import de.uka.ilkd.key.logic.sort.*;


public class TestDeclParser extends TestCase {

    NamespaceSet nss;
    Services serv;

    public TestDeclParser(String name) {
	super(name);
    }

    public void setUp() {
	nss = new NamespaceSet();
	serv = new Services ();
	Recoder2KeY r2k = new Recoder2KeY(serv, nss);
	r2k.parseSpecialClasses();
    }

    private KeYParser stringParser(String s) {
	return new KeYParser(ParserMode.DECLARATION, new KeYLexer(new StringReader(s),null),
			      "No file. Call of parser from parser/TestDeclParser.java",
			      serv, nss);
    }

    public void parseDecls(String s) {
	try {
	    KeYParser p = stringParser(s);
	    p.decls();
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


    protected GenericSort checkGenericSort ( Named            p_n,
					     SetOfSort        p_ext,
					     SetOfSort        p_oneof ) {
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


    public void testGenericSortDecl() {
	Named       n;
	GenericSort G, H;
	Sort        S, T;
	
	nss = new NamespaceSet ();
	parseDecls("\\sorts { \\generic G; \\generic H \\extends G; }");

	G = checkGenericSort ( nss.sorts().lookup(new Name("G")),
			       SetAsListOfSort.EMPTY_SET,
			       SetAsListOfSort.EMPTY_SET );
	H = checkGenericSort ( nss.sorts().lookup(new Name("H")),
			       SetAsListOfSort.EMPTY_SET.add ( G ),
			       SetAsListOfSort.EMPTY_SET );


	nss = new NamespaceSet ();
	parseDecls("\\sorts { S; \\generic G; \\generic H \\extends G, S; }");
	
	S = checkSort        ( nss.sorts().lookup(new Name("S")) );
	G = checkGenericSort ( nss.sorts().lookup(new Name("G")),
			       SetAsListOfSort.EMPTY_SET,
			       SetAsListOfSort.EMPTY_SET );
	H = checkGenericSort ( nss.sorts().lookup(new Name("H")),
			       SetAsListOfSort.EMPTY_SET.add ( S ).add ( G ),
			       SetAsListOfSort.EMPTY_SET );


	nss = new NamespaceSet ();
	parseDecls("\\sorts { S; T; \\generic H \\oneof {S, T}; }");

	S = checkSort        ( nss.sorts().lookup(new Name("S")) );
	T = checkSort        ( nss.sorts().lookup(new Name("T")) );
	H = checkGenericSort ( nss.sorts().lookup(new Name("H")),
			       SetAsListOfSort.EMPTY_SET,
			       SetAsListOfSort.EMPTY_SET.add ( S ).add ( T ) );
	

	nss = new NamespaceSet ();
	parseDecls("\\sorts { S; T; \\generic G; \\generic H \\oneof {S} \\extends T, G; }");

	S = checkSort        ( nss.sorts().lookup(new Name("S")) );
	T = checkSort        ( nss.sorts().lookup(new Name("T")) );
	G = checkGenericSort ( nss.sorts().lookup(new Name("G")),
			       SetAsListOfSort.EMPTY_SET,
			       SetAsListOfSort.EMPTY_SET );
	H = checkGenericSort ( nss.sorts().lookup(new Name("H")),
			       SetAsListOfSort.EMPTY_SET.add ( T ).add ( G ),
			       SetAsListOfSort.EMPTY_SET.add ( S ) );
	

	nss = new NamespaceSet ();
	parseDecls("\\sorts { S, T; \\generic G,G2; \\generic H,H2 \\oneof {S} \\extends T, G; }");

	S = checkSort        ( nss.sorts().lookup(new Name("S")) );
	T = checkSort        ( nss.sorts().lookup(new Name("T")) );
	G = checkGenericSort ( nss.sorts().lookup(new Name("G")),
			       SetAsListOfSort.EMPTY_SET,
			       SetAsListOfSort.EMPTY_SET );
	checkGenericSort     ( nss.sorts().lookup(new Name("G2")),
			       SetAsListOfSort.EMPTY_SET,
			       SetAsListOfSort.EMPTY_SET );
	H = checkGenericSort ( nss.sorts().lookup(new Name("H")),
			       SetAsListOfSort.EMPTY_SET.add ( T ).add ( G ),
			       SetAsListOfSort.EMPTY_SET.add ( S ) );
	checkGenericSort     ( nss.sorts().lookup(new Name("H2")),
			       SetAsListOfSort.EMPTY_SET.add ( T ).add ( G ),
			       SetAsListOfSort.EMPTY_SET.add ( S ) );
	

	nss = new NamespaceSet ();
	String str = "\\sorts { \\generic G; \\generic H \\oneof {G}; }";
	try {
	    KeYParser p = stringParser(str);
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

	assertTrue(msg, ((SchemaVariable)o).isVariableSV());
    }

    /** asserts that the SchemaVariable matches to term but not to a
     * formula 
     */
    public void assertTermSV(String msg, 
			     Object o) {

	assertTrue("The named object: "+o+" is of type "+o.getClass()+
		   ", but the type SchemaVariable was expected",
		   o instanceof SchemaVariable);
	assertSame(msg,
		   ((SchemaVariable)o).matchType(), Term.class);
	assertTrue("Schemavariable is not allowed to match a term of sort FORMULA.",
		   ((SortedSchemaVariable)o).sort() != Sort.FORMULA);
    }

    /** asserts that the SchemaVariable matches to a formula 
     * and not to a term (of sort != Sort.FORMULA)
     */
    public void assertFormulaSV(String msg, 
				Object o) {
	assertTrue("The named object: "+o+" is of type "+o.getClass()+
		   ", but the type SchemaVariable was expected",
		   o instanceof SchemaVariable);
	assertSame(msg,
		   ((SchemaVariable)o).matchType(), Term.class);
	assertSame("Only matches to terms of sort FORMULA allowed. "+
		   "But term has sort "+((SortedSchemaVariable)o).sort(), 
		   ((SortedSchemaVariable)o).sort(), Sort.FORMULA);

	
    }
  
    public void testArrayDecl() {
	parseDecls("\\sorts { aSort;}\n" +
		   "\\functions {\n" +
		   "  aSort[][] f(aSort);\n" +
		   "}\n");
	Sort aSort = (Sort)nss.sorts().lookup(new Name("aSort"));
	Sort objectSort = serv.getJavaInfo().getJavaLangObjectAsSort();
	Sort cloneableSort = serv.getJavaInfo().getJavaLangCloneableAsSort();
        Sort serializableSort = serv.getJavaInfo().getJavaIoSerializableAsSort();
	Sort aSortArr = ArraySortImpl.getArraySort(aSort, objectSort, cloneableSort, serializableSort);
	Sort aSortArr2 = ArraySortImpl.getArraySort(aSortArr, objectSort, cloneableSort, serializableSort);
	assertTrue("aSort[] should extend Cloneable ", 
		   aSortArr.extendsSorts().contains(cloneableSort)); 
 	assertTrue("aSort[] should transitively extend Object ", 
		   aSortArr.extendsTrans(objectSort)); 
  	assertTrue("aSort[][] should transitively extend Object ", 
		   aSortArr2.extendsTrans(objectSort)); 
  	assertTrue("aSort[][] should transitively extend Cloneable ", 
		   aSortArr2.extendsTrans(cloneableSort));
	assertTrue("aSort[][] should extend Cloneable[] ", 
		   aSortArr2.extendsSorts().contains
		   (ArraySortImpl.getArraySort(cloneableSort, objectSort, cloneableSort, serializableSort)));
  	assertTrue("Cloneable should extend Object ", 
		   cloneableSort.extendsSorts().contains(objectSort));
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
	
	Sort elem = (Sort)nss.sorts().lookup(new Name("elem"));
	Sort list = (Sort)nss.sorts().lookup(new Name("list"));

        Sort objectSort = serv.getJavaInfo().getJavaLangObjectAsSort();
        Sort cloneableSort = serv.getJavaInfo().getJavaLangCloneableAsSort();
        Sort serializableSort = serv.getJavaInfo().getJavaIoSerializableAsSort();
        
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
                ArraySortImpl.getArraySort(elem, objectSort, cloneableSort, serializableSort),

		     ((Function)nss.functions().lookup(new Name("tailarray"))).argSort(0));
	assertEquals("tailarray return sort", ArraySortImpl.getArraySort(elem, 
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
	
	Sort elem = (Sort)nss.sorts().lookup(new Name("elem"));
	Sort list = (Sort)nss.sorts().lookup(new Name("list"));


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
	
	
	Sort elem = (Sort)nss.sorts().lookup(new Name("elem"));
	Sort list = (Sort)nss.sorts().lookup(new Name("list"));

	assertEquals("find SV x", new Name("x"),
		     nss.variables().lookup(new Name("x")).name()); 
	assertTermSV("SV x type", 
		     nss.variables().lookup(new Name("x"))); 
	assertEquals("SV x sort", elem,
		     ((SortedSchemaVariable)nss.variables().lookup(new Name("x"))).sort()); 

	assertEquals("find SV ", new Name("y"),
		     nss.variables().lookup(new Name("y")).name()); 
	assertTermSV("SV y type", 
		     nss.variables().lookup(new Name("y"))); 
	assertEquals("SV y sort", elem,
		     ((SortedSchemaVariable)nss.variables().lookup(new Name("y"))).sort()); 

	assertEquals("find SV ", new Name("lv"),
		     nss.variables().lookup(new Name("lv")).name()); 
	assertVariableSV("SV lv type", 
		     nss.variables().lookup(new Name("lv"))); 
	assertEquals("SV lv sort", list,
		     ((SortedSchemaVariable)nss.variables().lookup(new Name("lv"))).sort()); 
	
	assertEquals("find SV ", new Name("b"),
		     nss.variables().lookup(new Name("b")).name()); 
	assertFormulaSV("SV b type", 
		     nss.variables().lookup(new Name("b"))); 
	assertEquals("SV b sort", Sort.FORMULA,
		     ((SortedSchemaVariable)nss.variables().lookup(new Name("b"))).sort()); 
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
	} catch (AmbigiousDeclException ade) {
	    // everything ok  
	} catch(RuntimeException e){
	    if(!(e.getCause() instanceof AmbigiousDeclException)){
		fail("Unexpected excpetion. Testcase failed." +e);
	    }
	}catch(antlr.TokenStreamException tse) {
	    fail("Unexpected excpetion. Testcase failed." + tse);
	} catch(antlr.RecognitionException re) {
	    fail("Unexpected excpetion. Testcase failed." + re);
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
    
