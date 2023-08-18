/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

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

import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


/**
 * Test cases for validating the correct handling of declarations inside KeY files.
 */
public class TestDeclParser {
    private NamespaceSet nss;
    private Services serv;
    private Namespace<SchemaVariable> parsedSchemaVars;
    private KeyIO io;

    @BeforeEach
    public void setUp() {
        serv = new Services(AbstractProfile.getDefaultProfile());
        nss = serv.getNamespaces();
        io = new KeyIO(serv, nss);
        NamespaceBuilder nb = new NamespaceBuilder(nss);
        nb.addSort("boolean").addSort("int").addSort("Seq").addSort("LocSet").addSort("double")
                .addSort("float");
        // String sorts = "\\sorts{boolean;int;LocSet;}";
        // parseDecls(sorts);
        assertNotNull(nss.sorts().lookup("boolean"));
        assertNotNull(nss.sorts().lookup("int"));
        assertNotNull(nss.sorts().lookup("boolean"));
        Recoder2KeY r2k = new Recoder2KeY(serv, nss);
        r2k.parseSpecialClasses();
    }

    private void evaluateDeclarations(String s) {
        try {
            KeyIO.Loader l = io.load(s);
            l.parseFile().loadDeclarations().loadSndDegreeDeclarations().loadTaclets();
            parsedSchemaVars = l.getSchemaNamespace();
        } catch (Exception e) {
            throw new RuntimeException("'" + s + "' was not parseable and evaluatable", e);
        }
    }


    @Test
    public void testSortDecl() {
        evaluateDeclarations("\\sorts { elem; list; }");
        assertEquals(new Name("elem"), nss.sorts().lookup(new Name("elem")).name(),
            "find sort elem");
        assertEquals(new Name("list"), nss.sorts().lookup(new Name("list")).name(),
            "find sort list");
    }

    private GenericSort checkGenericSort(Named name, ImmutableSet<Sort> pExt,
            ImmutableSet<Sort> pOneOf) {
        assertNotNull(name, "Generic sort does not exist");
        assertTrue(name instanceof GenericSort,
            "Generic sort does not have type GenericSort, but " + name.getClass());
        GenericSort gs = (GenericSort) name;

        assertEquals(pExt, gs.extendsSorts(), "Generic sort has wrong supersorts");

        assertEquals(pOneOf, gs.getOneOf(), "Generic sort has wrong oneof-list");

        return gs;
    }

    private Sort checkSort(Named name) {
        assertNotNull(name, "Sort does not exist");
        assertTrue(name instanceof Sort, "Sort does not have type Sort, but " + name.getClass());
        return (Sort) name;
    }

    @Test
    public void testProxySortDecl() {
        evaluateDeclarations(
            "\\sorts { A; B; \\proxy P; \\proxy Q \\extends A,B; \\proxy R \\extends Q; }");

        Sort P = nss.sorts().lookup(new Name("P"));
        assertNotNull(P);
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
            DefaultImmutableSet.<Sort>nil().add(Sort.ANY), DefaultImmutableSet.nil());
        H = checkGenericSort(nss.sorts().lookup(new Name("H")),
            DefaultImmutableSet.<Sort>nil().add(G), DefaultImmutableSet.nil());
    }

    @Test
    public void testGenericSortDecl2() {
        evaluateDeclarations("\\sorts { S; \\generic G; \\generic H \\extends G, S; }");

        Sort S = checkSort(nss.sorts().lookup(new Name("S")));
        GenericSort G = checkGenericSort(nss.sorts().lookup(new Name("G")),
            DefaultImmutableSet.<Sort>nil().add(Sort.ANY), DefaultImmutableSet.nil());
        GenericSort H = checkGenericSort(nss.sorts().lookup(new Name("H")),
            DefaultImmutableSet.<Sort>nil().add(S).add(G), DefaultImmutableSet.nil());
    }

    @Test
    public void testGenericSortDecl3() {
        evaluateDeclarations("\\sorts { S; T; \\generic H \\oneof {S, T}; }");

        Sort S = checkSort(nss.sorts().lookup(new Name("S")));
        Sort T = checkSort(nss.sorts().lookup(new Name("T")));
        GenericSort H = checkGenericSort(nss.sorts().lookup(new Name("H")),
            DefaultImmutableSet.<Sort>nil().add(Sort.ANY),
            DefaultImmutableSet.<Sort>nil().add(S).add(T));
    }

    @Test
    public void testGenericSortDecl6() {
        evaluateDeclarations(
            "\\sorts { S; T; \\generic G; \\generic H \\oneof {S} \\extends T, G; }");

        Sort S = checkSort(nss.sorts().lookup(new Name("S")));
        Sort T = checkSort(nss.sorts().lookup(new Name("T")));
        GenericSort G = checkGenericSort(nss.sorts().lookup(new Name("G")),
            DefaultImmutableSet.<Sort>nil().add(Sort.ANY), DefaultImmutableSet.nil());
        GenericSort H = checkGenericSort(nss.sorts().lookup(new Name("H")),
            DefaultImmutableSet.<Sort>nil().add(T).add(G), DefaultImmutableSet.<Sort>nil().add(S));

    }

    @Test
    public void testGenericSortDecl4() {
        evaluateDeclarations(
            "\\sorts { S, T; \\generic G,G2; \\generic H,H2 \\oneof {S} \\extends T, G; }");

        Sort S = checkSort(nss.sorts().lookup(new Name("S")));
        Sort T = checkSort(nss.sorts().lookup(new Name("T")));
        GenericSort G = checkGenericSort(nss.sorts().lookup(new Name("G")),
            DefaultImmutableSet.<Sort>nil().add(Sort.ANY), DefaultImmutableSet.nil());
        checkGenericSort(nss.sorts().lookup(new Name("G2")),
            DefaultImmutableSet.<Sort>nil().add(Sort.ANY), DefaultImmutableSet.nil());
        GenericSort H = checkGenericSort(nss.sorts().lookup(new Name("H")),
            DefaultImmutableSet.<Sort>nil().add(T).add(G), DefaultImmutableSet.<Sort>nil().add(S));
        checkGenericSort(nss.sorts().lookup(new Name("H2")),
            DefaultImmutableSet.<Sort>nil().add(T).add(G), DefaultImmutableSet.<Sort>nil().add(S));


    }

    @Test
    @Disabled
    // weigl: this test case seems not suitable anymore.
    // old parser throw an error message if generic sorts were used in normal mode.
    public void testGenericSortDecl5() {
        String str = "\\sorts { \\generic G; \\generic H \\oneof {G}; }";
        try {
            new KeyIO(serv, nss).load(str).loadDeclarations();
            fail("Expected an GenericSortException");
        } catch (Exception e) {
            System.out.println(e);
            assertTrue(e.getMessage().contains("generic"), "Expected a GenericSortException");
        }
    }

    /**
     * asserts that the found object is a schemavariable and that the allowed macthing type is
     * QuantifiableVariable
     */
    private void assertVariableSV(String msg, Object o) {
        assertTrue(o instanceof SchemaVariable, "The named object: " + o + " is of type "
            + o.getClass() + ", but the type SchemaVariable was expected");

        assertTrue(o instanceof VariableSV, msg);
    }

    /**
     * asserts that the SchemaVariable matches to term but not to a formula
     */
    private void assertTermSV(String msg, Object o) {

        assertTrue(o instanceof SchemaVariable, "The named object: " + o + " is of type "
            + o.getClass() + ", but the type SchemaVariable was expected");
        assertNotSame(((SchemaVariable) o).sort(), Sort.FORMULA,
            "Schemavariable is not allowed to match a term of sort FORMULA.");
    }

    /**
     * asserts that the SchemaVariable matches to a formula and not to a term (of sort !=
     * Sort.FORMULA)
     */
    private void assertFormulaSV(String msg, Object o) {
        assertTrue(o instanceof SchemaVariable, "The named object: " + o + " is of type "
            + o.getClass() + ", but the type SchemaVariable was expected");
        assertSame(((SchemaVariable) o).sort(), Sort.FORMULA,
            "Only matches to terms of sort FORMULA allowed. " + "But term has sort "
                + ((SchemaVariable) o).sort());


    }

    @Test
    public void testArrayDecl() {
        evaluateDeclarations(
            "\\sorts { aSort;}\n" + "\\functions {\n" + "  aSort[][] f(aSort);\n" + "}\n");
        Sort aSort = nss.sorts().lookup(new Name("aSort"));
        Sort objectSort = serv.getJavaInfo().objectSort();
        Sort cloneableSort = serv.getJavaInfo().cloneableSort();
        Sort serializableSort = serv.getJavaInfo().serializableSort();
        Sort aSortArr = ArraySort.getArraySort(aSort, objectSort, cloneableSort, serializableSort);
        Sort aSortArr2 =
            ArraySort.getArraySort(aSortArr, objectSort, cloneableSort, serializableSort);
        assertTrue(aSortArr.extendsSorts().contains(cloneableSort),
            "aSort[] should extend Cloneable: " + aSortArr.extendsSorts());
        assertTrue(aSortArr.extendsTrans(objectSort), "aSort[] should transitively extend Object ");
        assertTrue(aSortArr2.extendsTrans(objectSort),
            "aSort[][] should transitively extend Object ");
        assertTrue(aSortArr2.extendsTrans(cloneableSort),
            "aSort[][] should transitively extend Cloneable ");
        assertTrue(
            aSortArr2.extendsSorts().contains(
                ArraySort.getArraySort(cloneableSort, objectSort, cloneableSort, serializableSort)),
            "aSort[][] should extend Cloneable[] ");
        assertTrue(cloneableSort.extendsSorts().contains(objectSort),
            "Cloneable should extend Object ");
    }

    @Test
    public void testFunctionDecl() {
        evaluateDeclarations("\\sorts { elem; list; }\n" + "\\functions {\n"
            + "  elem head(list);\n" + "  list tail(list);\n" + "  elem[] tailarray(elem[]);\n"
            + "  list nil;\n" + "  list cons(elem,list);\n" + "}\n");

        Sort elem = nss.sorts().lookup(new Name("elem"));
        Sort list = nss.sorts().lookup(new Name("list"));

        Sort objectSort = serv.getJavaInfo().objectSort();
        Sort cloneableSort = serv.getJavaInfo().cloneableSort();
        Sort serializableSort = serv.getJavaInfo().serializableSort();

        assertEquals(new Name("head"), nss.functions().lookup(new Name("head")).name(),
            "find head function");
        assertEquals(1, nss.functions().lookup(new Name("head")).arity(), "head arity");
        assertEquals(list, nss.functions().lookup(new Name("head")).argSort(0), "head arg sort 0");
        assertEquals(elem, nss.functions().lookup(new Name("head")).sort(), "head return sort");

        assertEquals(new Name("tail"), nss.functions().lookup(new Name("tail")).name(),
            "find tail function");
        assertEquals(1, nss.functions().lookup(new Name("tail")).arity(), "tail arity");
        assertEquals(list, nss.functions().lookup(new Name("tail")).argSort(0), "tail arg sort 0");
        assertEquals(list, nss.functions().lookup(new Name("tail")).sort(), "tail return sort");
        assertEquals(ArraySort.getArraySort(elem, objectSort, cloneableSort, serializableSort),
            nss.functions().lookup(new Name("tailarray")).argSort(0), "tailarray arg sort 0");
        assertEquals(ArraySort.getArraySort(elem, objectSort, cloneableSort, serializableSort),
            nss.functions().lookup(new Name("tailarray")).sort(), "tailarray return sort");

        assertEquals(new Name("nil"), nss.functions().lookup(new Name("nil")).name(),
            "find nil function");
        assertEquals(0, nss.functions().lookup(new Name("nil")).arity(), "nil arity");
        assertEquals(list, nss.functions().lookup(new Name("nil")).sort(), "nil return sort");

        assertEquals(new Name("cons"), nss.functions().lookup(new Name("cons")).name(),
            "find cons function");
        assertEquals(2, nss.functions().lookup(new Name("cons")).arity(), "cons arity");
        assertEquals(elem, nss.functions().lookup(new Name("cons")).argSort(0), "cons arg sort 0");
        assertEquals(list, nss.functions().lookup(new Name("cons")).argSort(1), "cons arg sort 1");
        assertEquals(list, nss.functions().lookup(new Name("cons")).sort(), "cons return sort");
    }

    @Test
    public void testPredicateDecl() {
        evaluateDeclarations("\\sorts { elem; list; }\n" + "\\predicates {\n" + "  isEmpty(list);\n"
            + "  contains(list,elem);\n" + "  maybe;\n" + "}\n");

        Sort elem = nss.sorts().lookup(new Name("elem"));
        Sort list = nss.sorts().lookup(new Name("list"));


        assertEquals(new Name("isEmpty"), nss.functions().lookup(new Name("isEmpty")).name(),
            "find isEmpty predicate");
        assertEquals(1, nss.functions().lookup(new Name("isEmpty")).arity(), "isEmpty arity");
        assertEquals(list, nss.functions().lookup(new Name("isEmpty")).argSort(0),
            "isEmpty arg sort 0");
        assertEquals(Sort.FORMULA, nss.functions().lookup(new Name("isEmpty")).sort(),
            "isEmpty return sort");

        assertEquals(new Name("contains"), nss.functions().lookup(new Name("contains")).name(),
            "find contains predicate");
        assertEquals(2, nss.functions().lookup(new Name("contains")).arity(), "contains arity");
        assertEquals(list, nss.functions().lookup(new Name("contains")).argSort(0),
            "contains arg sort 0");
        assertEquals(elem, nss.functions().lookup(new Name("contains")).argSort(1),
            "contains arg sort 1");
        assertEquals(Sort.FORMULA, nss.functions().lookup(new Name("contains")).sort(),
            "contains return sort");

        assertEquals(new Name("maybe"), nss.functions().lookup(new Name("maybe")).name(),
            "find maybe predicate");
        assertEquals(0, nss.functions().lookup(new Name("maybe")).arity(), "maybe arity");
        assertEquals(Sort.FORMULA, nss.functions().lookup(new Name("maybe")).sort(),
            "maybe return sort");
    }

    @Test
    public void testSVDecl() {
        evaluateDeclarations(
            "\\sorts { elem; list; } " + "\\schemaVariables {" + "  \\program Statement #s ;"
                + "  \\term elem x,y ;" + "  \\variables list lv;" + "  \\formula b;}");


        Sort elem = nss.sorts().lookup(new Name("elem"));
        Sort list = nss.sorts().lookup(new Name("list"));

        Namespace<SchemaVariable> variables = parsedSchemaVars;

        assertEquals(new Name("x"), variables.lookup(new Name("x")).name(), "find SV x");
        assertTermSV("SV x type", variables.lookup(new Name("x")));
        assertEquals(elem, variables.lookup(new Name("x")).sort(), "SV x sort");

        assertEquals(new Name("y"), variables.lookup(new Name("y")).name(), "find SV ");
        assertTermSV("SV y type", variables.lookup(new Name("y")));
        assertEquals(elem, variables.lookup(new Name("y")).sort(), "SV y sort");

        assertEquals(new Name("lv"), variables.lookup(new Name("lv")).name(), "find SV ");
        assertVariableSV("SV lv type", variables.lookup(new Name("lv")));
        assertEquals(list, variables.lookup(new Name("lv")).sort(), "SV lv sort");

        assertEquals(new Name("b"), variables.lookup(new Name("b")).name(), "find SV ");
        assertFormulaSV("SV b type", variables.lookup(new Name("b")));
        assertEquals(Sort.FORMULA, variables.lookup(new Name("b")).sort(), "SV b sort");
    }


    @Test
    @Disabled("weigl: nparser handles the parsing differently. No Exception is thrown.")
    public void testAmbiguousDecls() {
        try {
            evaluateDeclarations("\\sorts { elem; list; }\n" + "\\functions {" + "elem x;"
                + "elem fn;" + "elem p;" + "}" + "\\predicates {" + "fn(elem);" + "y;" + "p;" + "}"
                + "\\schemaVariables {\n" + "  \\program Statement #s ; \n"
                + "  \\term elem x,y ;\n" + "  \\variables list lv ;\n" + "  \\formula b;\n"
                + "}\n");
            fail("Ambiguous declaration successfully parsed. Error was expected.");
            // FIXME nparser It seems that the nparser does not check for conflicting declarations
        } catch (RuntimeException e) {
            fail("Unexpected excpetion. Testcase failed.", e);
        }
    }

    @Test
    public void testHeurDecl() {
        evaluateDeclarations("\\heuristicsDecl { bool; shoot_foot; }");
        assertEquals(new Name("bool"), nss.ruleSets().lookup(new Name("bool")).name(),
            "find heuristic bool");
        assertEquals(new Name("shoot_foot"), nss.ruleSets().lookup(new Name("shoot_foot")).name(),
            "find heuristic shoot_foot");
    }
}
