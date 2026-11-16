/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.parser;


import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ArraySort;
import de.uka.ilkd.key.logic.sort.GenericSort;
import de.uka.ilkd.key.logic.sort.ProxySort;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.nparser.NamespaceBuilder;
import de.uka.ilkd.key.proof.init.AbstractProfile;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.Function;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.DefaultImmutableSet;
import org.key_project.util.collection.ImmutableSet;

import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;


/**
 * Test cases for validating the correct handling of declarations inside KeY files.
 */
public class TestDeclParser {
    // lazily created in setUp(); null until then
    private static @Nullable Services SERVICES = null;
    private NamespaceSet nss;
    private Services serv;
    // set by evaluateDeclarations(); null until then
    private @Nullable Namespace<SchemaVariable> parsedSchemaVars;
    private KeyIO io;

    @BeforeEach
    public void setUp() {
        if (SERVICES == null) {
            SERVICES = new Services(AbstractProfile.getDefaultProfile());
            var nss = SERVICES.getNamespaces();
            NamespaceBuilder nb = new NamespaceBuilder(nss);
            nb.addSort("boolean").addSort("int").addSort("Seq").addSort("LocSet").addSort("double")
                    .addSort("float");
            assertNotNull(nss.sorts().lookup("boolean"));
            assertNotNull(nss.sorts().lookup("int"));
            assertNotNull(nss.sorts().lookup("boolean"));
            SERVICES.activateJava(null);
            SERVICES.getJavaService().parseSpecialClasses();
        }
        serv = SERVICES.copy(false);
        nss = serv.getNamespaces();
        io = new KeyIO(serv, nss);
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
        Sort elem = Objects
                .requireNonNull(nss.sorts().lookup(new Name("elem")), "sort elem must exist");
        Sort list = Objects
                .requireNonNull(nss.sorts().lookup(new Name("list")), "sort list must exist");
        assertEquals(new Name("elem"), elem.name(), "find sort elem");
        assertEquals(new Name("list"), list.name(), "find sort list");
    }

    private GenericSort checkGenericSort(@Nullable Named name, ImmutableSet<Sort> pExt,
            ImmutableSet<Sort> pOneOf) {
        assertNotNull(name, "Generic sort does not exist");
        assertTrue(name instanceof GenericSort,
            "Generic sort does not have type GenericSort, but " + name.getClass());
        GenericSort gs = (GenericSort) name;

        assertEquals(pExt, gs.extendsSorts(), "Generic sort has wrong supersorts");

        assertEquals(pOneOf, gs.getOneOf(), "Generic sort has wrong oneof-list");

        return gs;
    }

    private Sort checkSort(@Nullable Named name) {
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
        assertEquals(DefaultImmutableSet.nil().add(JavaDLTheory.ANY), P.extendsSorts());

        Sort A = Objects.requireNonNull(nss.sorts().lookup(new Name("A")), "sort A must exist");
        Sort B = Objects.requireNonNull(nss.sorts().lookup(new Name("B")), "sort B must exist");
        Sort Q = nss.sorts().lookup(new Name("Q"));
        assertTrue(Q instanceof ProxySort);
        assertEquals("Q", Q.name().toString());
        assertEquals(DefaultImmutableSet.nil().add(A).add(B), Q.extendsSorts());

        Sort R = Objects.requireNonNull(nss.sorts().lookup(new Name("R")), "sort R must exist");
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
            DefaultImmutableSet.<Sort>nil().add(JavaDLTheory.ANY), DefaultImmutableSet.nil());
        H = checkGenericSort(nss.sorts().lookup(new Name("H")),
            DefaultImmutableSet.<Sort>nil().add(G), DefaultImmutableSet.nil());
    }

    @Test
    public void testGenericSortDecl2() {
        evaluateDeclarations("\\sorts { S; \\generic G; \\generic H \\extends G, S; }");

        Sort S = checkSort(nss.sorts().lookup(new Name("S")));
        GenericSort G = checkGenericSort(nss.sorts().lookup(new Name("G")),
            DefaultImmutableSet.<Sort>nil().add(JavaDLTheory.ANY), DefaultImmutableSet.nil());
        GenericSort H = checkGenericSort(nss.sorts().lookup(new Name("H")),
            DefaultImmutableSet.<Sort>nil().add(S).add(G), DefaultImmutableSet.nil());
    }

    @Test
    public void testGenericSortDecl3() {
        evaluateDeclarations("\\sorts { S; T; \\generic H \\oneof {S, T}; }");

        Sort S = checkSort(nss.sorts().lookup(new Name("S")));
        Sort T = checkSort(nss.sorts().lookup(new Name("T")));
        GenericSort H = checkGenericSort(nss.sorts().lookup(new Name("H")),
            DefaultImmutableSet.<Sort>nil().add(JavaDLTheory.ANY),
            DefaultImmutableSet.<Sort>nil().add(S).add(T));
    }

    @Test
    public void testGenericSortDecl6() {
        evaluateDeclarations(
            "\\sorts { S; T; \\generic G; \\generic H \\oneof {S} \\extends T, G; }");

        Sort S = checkSort(nss.sorts().lookup(new Name("S")));
        Sort T = checkSort(nss.sorts().lookup(new Name("T")));
        GenericSort G = checkGenericSort(nss.sorts().lookup(new Name("G")),
            DefaultImmutableSet.<Sort>nil().add(JavaDLTheory.ANY), DefaultImmutableSet.nil());
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
            DefaultImmutableSet.<Sort>nil().add(JavaDLTheory.ANY), DefaultImmutableSet.nil());
        checkGenericSort(nss.sorts().lookup(new Name("G2")),
            DefaultImmutableSet.<Sort>nil().add(JavaDLTheory.ANY), DefaultImmutableSet.nil());
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
            String message = Objects.requireNonNull(e.getMessage(), "the exception has a message");
            assertTrue(message.contains("generic"), "Expected a GenericSortException");
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
        assertTrue(o instanceof TermSV, "The named object: " + o + " is of type "
            + o.getClass() + ", but the type SchemaVariable was expected");
        assertNotSame(((TermSV) o).sort(), JavaDLTheory.FORMULA,
            "Schemavariable is not allowed to match a term of sort FORMULA.");
    }

    /**
     * asserts that the SchemaVariable matches to a formula and not to a term (of sort !=
     * Sort.FORMULA)
     */
    private void assertFormulaSV(String msg, Object o) {
        assertTrue(o instanceof FormulaSV, "The named object: " + o + " is of type "
            + o.getClass() + ", but the type SchemaVariable was expected");
        assertSame(((FormulaSV) o).sort(), JavaDLTheory.FORMULA,
            "Only matches to terms of sort FORMULA allowed. " + "But term has sort "
                + ((FormulaSV) o).sort());


    }

    @Test
    public void testArrayDecl() {
        evaluateDeclarations(
            """
                    \\sorts { aSort;}
                    \\functions {
                      aSort[][] f(aSort);
                    }
                    """);
        Sort aSort = Objects
                .requireNonNull(nss.sorts().lookup(new Name("aSort")), "sort aSort must exist");
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
        evaluateDeclarations("""
                \\sorts { elem; list; }
                \\functions {
                  elem head(list);
                  list tail(list);
                  elem[] tailarray(elem[]);
                  list nil;
                  list cons(elem,list);
                }
                """);

        Sort elem = Objects
                .requireNonNull(nss.sorts().lookup(new Name("elem")), "sort elem must exist");
        Sort list = nss.sorts().lookup(new Name("list"));

        Sort objectSort = serv.getJavaInfo().objectSort();
        Sort cloneableSort = serv.getJavaInfo().cloneableSort();
        Sort serializableSort = serv.getJavaInfo().serializableSort();

        Function head = Objects
                .requireNonNull(nss.functions().lookup(new Name("head")),
                    "function head must exist");
        assertEquals(new Name("head"), head.name(), "find head function");
        assertEquals(1, head.arity(), "head arity");
        assertEquals(list, head.argSort(0), "head arg sort 0");
        assertEquals(elem, head.sort(), "head return sort");

        Function tail = Objects
                .requireNonNull(nss.functions().lookup(new Name("tail")),
                    "function tail must exist");
        assertEquals(new Name("tail"), tail.name(), "find tail function");
        assertEquals(1, tail.arity(), "tail arity");
        assertEquals(list, tail.argSort(0), "tail arg sort 0");
        assertEquals(list, tail.sort(), "tail return sort");
        Function tailarray = Objects
                .requireNonNull(nss.functions().lookup(new Name("tailarray")),
                    "function tailarray must exist");
        assertEquals(ArraySort.getArraySort(elem, objectSort, cloneableSort, serializableSort),
            tailarray.argSort(0), "tailarray arg sort 0");
        assertEquals(ArraySort.getArraySort(elem, objectSort, cloneableSort, serializableSort),
            tailarray.sort(), "tailarray return sort");

        Function nil = Objects
                .requireNonNull(nss.functions().lookup(new Name("nil")),
                    "function nil must exist");
        assertEquals(new Name("nil"), nil.name(), "find nil function");
        assertEquals(0, nil.arity(), "nil arity");
        assertEquals(list, nil.sort(), "nil return sort");

        Function cons = Objects
                .requireNonNull(nss.functions().lookup(new Name("cons")),
                    "function cons must exist");
        assertEquals(new Name("cons"), cons.name(), "find cons function");
        assertEquals(2, cons.arity(), "cons arity");
        assertEquals(elem, cons.argSort(0), "cons arg sort 0");
        assertEquals(list, cons.argSort(1), "cons arg sort 1");
        assertEquals(list, cons.sort(), "cons return sort");
    }

    @Test
    public void testPredicateDecl() {
        evaluateDeclarations("""
                \\sorts { elem; list; }
                \\predicates {
                  isEmpty(list);
                  contains(list,elem);
                  maybe;
                }
                """);

        Sort elem = nss.sorts().lookup(new Name("elem"));
        Sort list = nss.sorts().lookup(new Name("list"));


        Function isEmpty = Objects
                .requireNonNull(nss.functions().lookup(new Name("isEmpty")),
                    "predicate isEmpty must exist");
        assertEquals(new Name("isEmpty"), isEmpty.name(), "find isEmpty predicate");
        assertEquals(1, isEmpty.arity(), "isEmpty arity");
        assertEquals(list, isEmpty.argSort(0), "isEmpty arg sort 0");
        assertEquals(JavaDLTheory.FORMULA, isEmpty.sort(), "isEmpty return sort");

        Function contains = Objects
                .requireNonNull(nss.functions().lookup(new Name("contains")),
                    "predicate contains must exist");
        assertEquals(new Name("contains"), contains.name(), "find contains predicate");
        assertEquals(2, contains.arity(), "contains arity");
        assertEquals(list, contains.argSort(0), "contains arg sort 0");
        assertEquals(elem, contains.argSort(1), "contains arg sort 1");
        assertEquals(JavaDLTheory.FORMULA, contains.sort(), "contains return sort");

        Function maybe = Objects
                .requireNonNull(nss.functions().lookup(new Name("maybe")),
                    "predicate maybe must exist");
        assertEquals(new Name("maybe"), maybe.name(), "find maybe predicate");
        assertEquals(0, maybe.arity(), "maybe arity");
        assertEquals(JavaDLTheory.FORMULA, maybe.sort(), "maybe return sort");
    }

    @Test
    public void testSVDecl() {
        evaluateDeclarations(
            "\\sorts { elem; list; } " + "\\schemaVariables {" + "  \\program Statement #s ;"
                + "  \\term elem x,y ;" + "  \\variables list lv;" + "  \\formula b;}");


        Sort elem = nss.sorts().lookup(new Name("elem"));
        Sort list = nss.sorts().lookup(new Name("list"));

        Namespace<SchemaVariable> variables = Objects
                .requireNonNull(parsedSchemaVars, "the schema variables must have been parsed");

        SchemaVariable x =
            Objects.requireNonNull(variables.lookup(new Name("x")), "SV x must exist");
        assertEquals(new Name("x"), x.name(), "find SV x");
        assertTermSV("SV x type", x);
        assertEquals(elem, ((TermSV) x).sort(), "SV x sort");

        SchemaVariable y =
            Objects.requireNonNull(variables.lookup(new Name("y")), "SV y must exist");
        assertEquals(new Name("y"), y.name(), "find SV ");
        assertTermSV("SV y type", y);
        assertEquals(elem, ((TermSV) y).sort(), "SV y sort");

        SchemaVariable lv =
            Objects.requireNonNull(variables.lookup(new Name("lv")), "SV lv must exist");
        assertEquals(new Name("lv"), lv.name(), "find SV ");
        assertVariableSV("SV lv type", lv);
        assertEquals(list, ((VariableSV) lv).sort(), "SV lv sort");

        SchemaVariable b =
            Objects.requireNonNull(variables.lookup(new Name("b")), "SV b must exist");
        assertEquals(new Name("b"), b.name(), "find SV ");
        assertFormulaSV("SV b type", b);
        assertEquals(JavaDLTheory.FORMULA, ((FormulaSV) b).sort(), "SV b sort");
    }


    @Test
    @Disabled("weigl: nparser handles the parsing differently. No Exception is thrown.")
    public void testAmbiguousDecls() {
        try {
            evaluateDeclarations(
                """
                        \\sorts { elem; list; }
                        \\functions {elem x;elem fn;elem p;}\\predicates {fn(elem);y;p;}\\schemaVariables {
                          \\program Statement #s ;\s
                          \\term elem x,y ;
                          \\variables list lv ;
                          \\formula b;
                        }
                        """);
            fail("Ambiguous declaration successfully parsed. Error was expected.");
            // FIXME nparser It seems that the nparser does not check for conflicting declarations
        } catch (RuntimeException e) {
            fail("Unexpected excpetion. Testcase failed.", e);
        }
    }

    @Test
    public void testHeurDecl() {
        evaluateDeclarations("\\heuristicsDecl { bool; shoot_foot; }");
        var bool = Objects
                .requireNonNull(nss.ruleSets().lookup(new Name("bool")),
                    "rule set bool must exist");
        assertEquals(new Name("bool"), bool.name(), "find heuristic bool");
        var shootFoot = Objects
                .requireNonNull(nss.ruleSets().lookup(new Name("shoot_foot")),
                    "rule set shoot_foot must exist");
        assertEquals(new Name("shoot_foot"), shootFoot.name(), "find heuristic shoot_foot");
    }
}
