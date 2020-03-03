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

import org.antlr.runtime.RecognitionException;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.logic.op.VariableSV;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProxySort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.nparser.NamespaceBuilder;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import org.junit.Assert;
import org.junit.Before;
import org.junit.Ignore;
import org.junit.Test;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import static org.junit.Assert.*;


/**
 * Test cases for validating the correct handling of declarations inside KeY files.
 */
public class TestDeclParser {
    private NamespaceSet nss;
    private Services serv;
    private Namespace<SchemaVariable> parsedSchemaVars;
    private KeyIO io;

    @Before
    public void setUp() {
        serv = new Services(AbstractProfile.getDefaultProfile());
        nss = serv.getNamespaces();
        io = new KeyIO(serv, nss);
        NamespaceBuilder nb = new NamespaceBuilder(nss);
        nb.addSort("boolean")
                .addSort("int")
                .addSort("LocSet");
        //String sorts = "\\sorts{boolean;int;LocSet;}";
        //parseDecls(sorts);
        Assert.assertNotNull(nss.sorts().lookup("boolean"));
        Assert.assertNotNull(nss.sorts().lookup("int"));
        Assert.assertNotNull(nss.sorts().lookup("boolean"));
        Recoder2KeY r2k = new Recoder2KeY(serv, nss);
        r2k.parseSpecialClasses();
    }

    private void evaluateDeclarations(String s) {
        try {
            var l = io.load(s);
            l.parseFile().loadComplete();
            parsedSchemaVars = l.getSchemaNamespace();
        } catch (Exception e) {
            throw new RuntimeException("'" + s + "' was not parseable and evaluatable", e);
        }
    }


    @Test
    public void testSortDecl() {
        evaluateDeclarations("\\sorts { elem; list; }");
        assertEquals("find sort elem", new Name("elem"),
                nss.sorts().lookup(new Name("elem")).name());
        assertEquals("find sort list", new Name("list"),
                nss.sorts().lookup(new Name("list")).name());
    }

    private GenericSort checkGenericSort(Named name, ImmutableSet<Sort> pExt,
                                         ImmutableSet<Sort> pOneOf) {
        assertNotNull("Generic sort does not exist", name);
        assertTrue("Generic sort does not have type GenericSort, but " + name.getClass(),
                name instanceof GenericSort);
        GenericSort gs = (GenericSort) name;

        assertEquals("Generic sort has wrong supersorts",
                pExt,
                gs.extendsSorts());

        assertEquals("Generic sort has wrong oneof-list",
                pOneOf,
                gs.getOneOf());

        return gs;
    }

    private Sort checkSort(Named name) {
        assertNotNull("Sort does not exist", name);
        assertTrue("Sort does not have type Sort, but " + name.getClass(),
                name instanceof Sort);
        return (Sort) name;
    }

    @Test
    public void testProxySortDecl() {
        evaluateDeclarations("\\sorts { A; B; \\proxy P; \\proxy Q \\extends A,B; \\proxy R \\extends Q; }");

        Sort P = nss.sorts().lookup(new Name("P"));
        Assert.assertNotNull(P);
        assertTrue(P instanceof ProxySort);
        assertEquals("P", P.name().toString());
        assertEquals(DefaultImmutableSet.nil().add(Sort.ANY), P.extendsSorts());

        Sort A = nss.sorts().lookup(new Name("A"));
        Sort B = nss.sorts().lookup(new Name("B"));
        Sort Q = nss.sorts().lookup(new Name("Q"));
        assertTrue(Q instanceof ProxySort);
        assertEquals("Q", Q.name().toString());
        assertEquals(DefaultImmutableSet.nil().add(A).add(B), Q.extendsSorts());

        Sort R = nss.sorts().lookup(new Name("R"));
        assertTrue(P instanceof ProxySort);
        assertEquals("R", R.name().toString());
        assertEquals(DefaultImmutableSet.nil().add(Q), R.extendsSorts());
    }

    @Test
    public void testGenericSortDecl1() {
        GenericSort G, H;
        Sort S, T;

        evaluateDeclarations("\\sorts { \\generic G; \\generic H \\extends G; }");

        G = checkGenericSort(nss.sorts().lookup(new Name("G")),
                DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
                DefaultImmutableSet.nil());
        H = checkGenericSort(nss.sorts().lookup(new Name("H")),
                DefaultImmutableSet.<Sort>nil().add(G),
                DefaultImmutableSet.nil());
    }

    @Test
    public void testGenericSortDecl2() {
        evaluateDeclarations("\\sorts { S; \\generic G; \\generic H \\extends G, S; }");

        var S = checkSort(nss.sorts().lookup(new Name("S")));
        var G = checkGenericSort(nss.sorts().lookup(new Name("G")),
                DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
                DefaultImmutableSet.nil());
        var H = checkGenericSort(nss.sorts().lookup(new Name("H")),
                DefaultImmutableSet.<Sort>nil().add(S).add(G),
                DefaultImmutableSet.nil());
    }

    @Test
    public void testGenericSortDecl3() {
        evaluateDeclarations("\\sorts { S; T; \\generic H \\oneof {S, T}; }");

        var S = checkSort(nss.sorts().lookup(new Name("S")));
        var T = checkSort(nss.sorts().lookup(new Name("T")));
        var H = checkGenericSort(nss.sorts().lookup(new Name("H")),
                DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
                DefaultImmutableSet.<Sort>nil().add(S).add(T));
    }

    @Test
    public void testGenericSortDecl6() {
        evaluateDeclarations("\\sorts { S; T; \\generic G; \\generic H \\oneof {S} \\extends T, G; }");

        var S = checkSort(nss.sorts().lookup(new Name("S")));
        var T = checkSort(nss.sorts().lookup(new Name("T")));
        var G = checkGenericSort(nss.sorts().lookup(new Name("G")),
                DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
                DefaultImmutableSet.nil());
        var H = checkGenericSort(nss.sorts().lookup(new Name("H")),
                DefaultImmutableSet.<Sort>nil().add(T).add(G),
                DefaultImmutableSet.<Sort>nil().add(S));

    }

    @Test
    public void testGenericSortDecl4() {
        evaluateDeclarations("\\sorts { S, T; \\generic G,G2; \\generic H,H2 \\oneof {S} \\extends T, G; }");

        var S = checkSort(nss.sorts().lookup(new Name("S")));
        var T = checkSort(nss.sorts().lookup(new Name("T")));
        var G = checkGenericSort(nss.sorts().lookup(new Name("G")),
                DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
                DefaultImmutableSet.nil());
        checkGenericSort(nss.sorts().lookup(new Name("G2")),
                DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
                DefaultImmutableSet.nil());
        var H = checkGenericSort(nss.sorts().lookup(new Name("H")),
                DefaultImmutableSet.<Sort>nil().add(T).add(G),
                DefaultImmutableSet.<Sort>nil().add(S));
        checkGenericSort(nss.sorts().lookup(new Name("H2")),
                DefaultImmutableSet.<Sort>nil().add(T).add(G),
                DefaultImmutableSet.<Sort>nil().add(S));


    }

    @Test@Ignore
    //weigl: this test case seems not suitable anymore.
    // old parser throw an error message if generic sorts were used in normal mode.
    public void testGenericSortDecl5() {
        String str = "\\sorts { \\generic G; \\generic H \\oneof {G}; }";
        try {
            new KeyIO(serv, nss).load(str).loadDeclarations();
            fail("Expected an GenericSortException");
        } catch (Exception e) {
            assertTrue("Expected a GenericSortException",
                    e instanceof de.uka.ilkd.key.parser.GenericSortException || e.getCause() instanceof de.uka.ilkd.key.parser.GenericSortException);
        }
    }

    /**
     * asserts that the found object is a schemavariable and
     * that the allowed macthing type is QuantifiableVariable
     */
    private void assertVariableSV(String msg,
                                  Object o) {
        assertTrue("The named object: " + o + " is of type " + o.getClass() +
                        ", but the type SchemaVariable was expected",
                o instanceof SchemaVariable);

        assertTrue(msg, o instanceof VariableSV);
    }

    /**
     * asserts that the SchemaVariable matches to term but not to a
     * formula
     */
    private void assertTermSV(String msg, Object o) {

        assertTrue("The named object: " + o + " is of type " + o.getClass() +
                        ", but the type SchemaVariable was expected",
                o instanceof SchemaVariable);
        assertTrue("Schemavariable is not allowed to match a term of sort FORMULA.",
                ((SchemaVariable) o).sort() != Sort.FORMULA);
    }

    /**
     * asserts that the SchemaVariable matches to a formula
     * and not to a term (of sort != Sort.FORMULA)
     */
    private void assertFormulaSV(String msg, Object o) {
        assertTrue("The named object: " + o + " is of type " + o.getClass() +
                        ", but the type SchemaVariable was expected",
                o instanceof SchemaVariable);
        assertSame("Only matches to terms of sort FORMULA allowed. " +
                        "But term has sort " + ((SchemaVariable) o).sort(),
                ((SchemaVariable) o).sort(), Sort.FORMULA);


    }

    @Test
    public void testArrayDecl() {
        evaluateDeclarations("\\sorts { aSort;}\n" +
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

    @Test
    public void testFunctionDecl() {
        evaluateDeclarations("\\sorts { elem; list; }\n" +
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
                nss.functions().lookup(new Name("head")).arity());
        assertEquals("head arg sort 0", list,
                nss.functions().lookup(new Name("head")).argSort(0));
        assertEquals("head return sort", elem,
                nss.functions().lookup(new Name("head")).sort());

        assertEquals("find tail function", new Name("tail"),
                nss.functions().lookup(new Name("tail")).name());
        assertEquals("tail arity", 1,
                nss.functions().lookup(new Name("tail")).arity());
        assertEquals("tail arg sort 0", list,
                nss.functions().lookup(new Name("tail")).argSort(0));
        assertEquals("tail return sort", list,
                nss.functions().lookup(new Name("tail")).sort());
        assertEquals("tailarray arg sort 0",
                ArraySort.getArraySort(elem, objectSort, cloneableSort, serializableSort),

                nss.functions().lookup(new Name("tailarray")).argSort(0));
        assertEquals("tailarray return sort", ArraySort.getArraySort(elem,
                objectSort, cloneableSort, serializableSort),
                nss.functions().lookup(new Name("tailarray")).sort());

        assertEquals("find nil function", new Name("nil"),
                nss.functions().lookup(new Name("nil")).name());
        assertEquals("nil arity", 0,
                nss.functions().lookup(new Name("nil")).arity());
        assertEquals("nil return sort", list,
                nss.functions().lookup(new Name("nil")).sort());

        assertEquals("find cons function", new Name("cons"),
                nss.functions().lookup(new Name("cons")).name());
        assertEquals("cons arity", 2,
                nss.functions().lookup(new Name("cons")).arity());
        assertEquals("cons arg sort 0", elem,
                nss.functions().lookup(new Name("cons")).argSort(0));
        assertEquals("cons arg sort 1", list,
                nss.functions().lookup(new Name("cons")).argSort(1));
        assertEquals("cons return sort", list,
                nss.functions().lookup(new Name("cons")).sort());
    }

    @Test
    public void testPredicateDecl() {
        evaluateDeclarations("\\sorts { elem; list; }\n" +
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
                nss.functions().lookup(new Name("isEmpty")).arity());
        assertEquals("isEmpty arg sort 0", list,
                nss.functions().lookup(new Name("isEmpty")).argSort(0));
        assertEquals("isEmpty return sort", Sort.FORMULA,
                nss.functions().lookup(new Name("isEmpty")).sort());

        assertEquals("find contains predicate", new Name("contains"),
                nss.functions().lookup(new Name("contains")).name());
        assertEquals("contains arity", 2,
                nss.functions().lookup(new Name("contains")).arity());
        assertEquals("contains arg sort 0", list,
                nss.functions().lookup(new Name("contains")).argSort(0));
        assertEquals("contains arg sort 1", elem,
                nss.functions().lookup(new Name("contains")).argSort(1));
        assertEquals("contains return sort", Sort.FORMULA,
                nss.functions().lookup(new Name("contains")).sort());

        assertEquals("find maybe predicate", new Name("maybe"),
                nss.functions().lookup(new Name("maybe")).name());
        assertEquals("maybe arity", 0,
                nss.functions().lookup(new Name("maybe")).arity());
        assertEquals("maybe return sort", Sort.FORMULA,
                nss.functions().lookup(new Name("maybe")).sort());
    }

    @Test
    public void testSVDecl() {
        evaluateDeclarations("\\sorts { elem; list; } " +
                "\\schemaVariables {" +
                "  \\program Statement #s ;" +
                "  \\term elem x,y ;" +
                "  \\variables list lv;" +
                "  \\formula b;}");


        Sort elem = nss.sorts().lookup(new Name("elem"));
        Sort list = nss.sorts().lookup(new Name("list"));

        Namespace<SchemaVariable> variables = parsedSchemaVars;

        assertEquals("find SV x", new Name("x"),
                variables.lookup(new Name("x")).name());
        assertTermSV("SV x type",
                variables.lookup(new Name("x")));
        assertEquals("SV x sort", elem,
                variables.lookup(new Name("x")).sort());

        assertEquals("find SV ", new Name("y"),
                variables.lookup(new Name("y")).name());
        assertTermSV("SV y type",
                variables.lookup(new Name("y")));
        assertEquals("SV y sort", elem,
                variables.lookup(new Name("y")).sort());

        assertEquals("find SV ", new Name("lv"),
                variables.lookup(new Name("lv")).name());
        assertVariableSV("SV lv type",
                variables.lookup(new Name("lv")));
        assertEquals("SV lv sort", list,
                variables.lookup(new Name("lv")).sort());

        assertEquals("find SV ", new Name("b"),
                variables.lookup(new Name("b")).name());
        assertFormulaSV("SV b type",
                variables.lookup(new Name("b")));
        assertEquals("SV b sort", Sort.FORMULA,
                variables.lookup(new Name("b")).sort());
    }


    @Test
    @Ignore("weigl: nparser handles the parsing differently. No Exception is thrown.")
    public void testAmbiguousDecls() {
        try {
            evaluateDeclarations(
                    "\\sorts { elem; list; }\n" +
                            "\\functions {" +
                            "elem x;" +
                            "elem fn;" +
                            "elem p;" +
                            "}" +
                            "\\predicates {" +
                            "fn(elem);" +
                            "y;" +
                            "p;" +
                            "}" +
                            "\\schemaVariables {\n" +
                            "  \\program Statement #s ; \n" +
                            "  \\term elem x,y ;\n" +
                            "  \\variables list lv ;\n" +
                            "  \\formula b;\n" +
                            "}\n");
            fail("Ambiguous declaration successfully parsed. Error was expected.");
            //FIXME nparser It seems that the nparser does not check for conflicting declarations
        } catch (RuntimeException e) {
            if (!(e.getCause() instanceof AmbigiousDeclException)) {
                e.printStackTrace();
                fail("Unexpected excpetion. Testcase failed." + e);
            }
        }
    }

    @Test
    public void testHeurDecl() {
        evaluateDeclarations("\\heuristicsDecl { bool; shoot_foot; }");
        assertEquals("find heuristic bool",
                new Name("bool"),
                nss.ruleSets().lookup(new Name("bool")).name());
        assertEquals("find heuristic shoot_foot",
                new Name("shoot_foot"),
                nss.ruleSets().lookup(new Name("shoot_foot")).name());
    }
}
