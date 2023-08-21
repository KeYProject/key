/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import java.io.IOException;

import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.util.collection.ImmutableArray;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.*;

public class TestTermParser extends AbstractTestTermParser {
    private static final Logger LOGGER = LoggerFactory.getLogger(TestTermParser.class);

    private Sort elem, list;
    private Function head, tail, nil, cons, isempty;
    private LogicVariable x, y, z, xs, ys;
    private Term t_x, t_y, t_z, t_xs, t_ys;
    private Term t_headxs, t_tailys, t_nil;
    private final Recoder2KeY r2k;

    public TestTermParser() {
        r2k = new Recoder2KeY(services, nss);
        r2k.parseSpecialClasses();
        r2k.readCompilationUnit(COMPILATION_UNIT);
    }

    @Override
    protected Services getServices() {
        return TacletForTests.services();
    }

    @BeforeEach
    public void setUp() throws IOException {
        parseDecls("\\sorts { boolean; elem; list; int; int_sort; numbers;  }\n" + "\\functions {\n"
            + "  elem head(list);\n" + "  list tail(list);\n" + "  list nil;\n"
            + "  list cons(elem,list);\n" + "int aa ;\n" + "int bb ;\n" + "int cc ;\n"
            + "int dd ;\n" + "int ee ;\n" + "}\n" + "\\predicates {\n" + "  isempty(list);\n"
            + "}\n" + "\\programVariables {int globalIntPV;}"

        );

        elem = lookup_sort("elem");
        list = lookup_sort("list");
        head = lookup_func("head");
        tail = lookup_func("tail");
        nil = lookup_func("nil");
        cons = lookup_func("cons");
        isempty = lookup_func("isempty");

        // The declaration parser cannot parse LogicVariables; these
        // are normally declared in quantifiers, so we introduce them
        // ourselves!
        x = declareVar("x", elem);
        t_x = tf.createTerm(x);
        y = declareVar("y", elem);
        t_y = tf.createTerm(y);
        z = declareVar("z", elem);
        t_z = tf.createTerm(z);
        xs = declareVar("xs", list);
        t_xs = tf.createTerm(xs);
        ys = declareVar("ys", list);
        t_ys = tf.createTerm(ys);

        t_headxs = tf.createTerm(head, new Term[] { t_xs }, null, null);
        t_tailys = tf.createTerm(tail, new Term[] { t_ys }, null, null);
        t_nil = tf.createTerm(nil);

        assertNotNull(head);
        assertNotNull(elem);
        assertNotNull(tail);
        assertNotNull(nil);
        assertNotNull(cons);
        assertNotNull(isempty);
    }


    @Test
    public void test1() throws Exception {
        assertEquals(t_x, parseTerm("x"), "parse x");
    }

    @Test()
    public void test1a() {
        assertThrows(BuildingException.class, () -> parseTerm("x()"));
    }

    @Test
    public void test2() throws Exception {
        assertEquals(t_headxs, parseTerm("head(xs)"), "parse head(xs)");
    }

    @Test
    public void test3() throws Exception {
        Term t = tf.createTerm(cons, t_headxs, t_tailys);

        assertEquals(t, parseTerm("cons(head(xs),tail(ys))"), "parse cons(head(xs),tail(ys))");
    }

    @Test
    public void test5() throws Exception {
        Term t = tf.createTerm(Equality.EQUALS, tf.createTerm(head, tf.createTerm(cons, t_x, t_xs)),
            tf.createTerm(head, tf.createTerm(cons, t_x, t_nil)));

        assertEquals(t, parseFormula("head(cons(x,xs))=head(cons(x,nil))"),
            "parse head(cons(x,xs))=head(cons(x,nil))");
        assertEquals(t, parseFormula("head(cons(x,xs))=head(cons(x,nil()))"),
            "parse head(cons(x,xs))=head(cons(x,nil))");
    }

    @Test
    public void testNotEqual() throws Exception {
        Term t = tf.createTerm(Junctor.NOT,
            tf.createTerm(Equality.EQUALS, tf.createTerm(head, tf.createTerm(cons, t_x, t_xs)),
                tf.createTerm(head, tf.createTerm(cons, t_x, t_nil))));

        assertEquals(t, parseFormula("head(cons(x,xs))!=head(cons(x,nil))"),
            "parse head(cons(x,xs))!=head(cons(x,nil))");
    }

    @Test
    public void test6() throws Exception {
        Term t = tf.createTerm(Equality.EQV,
            new Term[] {
                tf.createTerm(Junctor.IMP,
                    tf.createTerm(Junctor.OR, tf.createTerm(Equality.EQUALS, t_x, t_x),
                        tf.createTerm(Equality.EQUALS, t_y, t_y)),
                    tf.createTerm(Junctor.AND, tf.createTerm(Equality.EQUALS, t_z, t_z),
                        tf.createTerm(Equality.EQUALS, t_xs, t_xs))),
                tf.createTerm(Junctor.NOT, tf.createTerm(Equality.EQUALS, t_ys, t_ys)) },
            null, null);


        assertEquals(t, parseFormula("x=x|y=y->z=z&xs=xs<->!ys=ys"),
            "parse x=x | y=y -> z=z & xs =xs <-> ! ys = ys");
    }

    @Test
    public void test7() throws Exception {
        /*
         * Bound variables are newly created by the parser, so we have to parse first, then extract
         * the used variables, then build the formulae.
         */

        String s = "\\forall list x; \\forall list l1; ! x = l1";
        Term t = parseFormula(s);

        LogicVariable thisx = (LogicVariable) t.varsBoundHere(0).get(0);
        LogicVariable l1 = (LogicVariable) t.sub(0).varsBoundHere(0).get(0);

        Term t1 = tb.all(thisx, tb.all(l1, tf.createTerm(Junctor.NOT,
            tf.createTerm(Equality.EQUALS, tf.createTerm(thisx), tf.createTerm(l1)))));

        assertNotSame(thisx, x, "new variable in quantifier");
        assertEquals(t1, t, "parse \\forall list x; \\forall list l1; ! x = l1");

    }

    @Test
    public void test8() throws Exception {
        /* A bit like test7, but for a substitution term */
        // String s = "{\\subst elem xs; head(xs)} cons(xs,ys)"; weigl: not well-typed
        String s = "{\\subst list y; tail(y)} head(xs)";
        Term t = parseTerm(s);
        Term xs = parseTerm("xs");

        LogicVariable thisxs = (LogicVariable) t.varsBoundHere(1).get(0);

        Term inner = tf.createTerm(head, xs); // head(xs)
        Term replacement = tf.createTerm(tail, tf.createTerm(thisxs)); // tail(xs)
        Term subst = tf.createTerm(WarySubstOp.SUBST, new Term[] { replacement, inner },
            new ImmutableArray<>(thisxs), null);

        assertNotSame(thisxs, xs);
        assertEquals(subst, t);
    }

    @Test
    public void test9() throws Exception {
        /* Try something with a prediate */
        String s = "\\exists list x; !isempty(x)";
        Term t = parseFormula(s);

        LogicVariable thisx = (LogicVariable) t.varsBoundHere(0).get(0);

        Term t1 = tb.ex(thisx, tf.createTerm(Junctor.NOT,
            tf.createTerm(isempty, new Term[] { tf.createTerm(thisx) }, null, null)));

        assertNotSame(thisx, x, "new variable in quantifier");
        assertEquals(t1, t, "parse \\forall list x; \\forall list l1; ! x = l1");

    }

    @Test
    public void test10() throws Exception {
        // Unquoted, this is
        // <{ int x = 2; {String x = "\"}";} }> true
        // String s = "< { int x = 1; {String s = \"\\\"}\";} } > true";
        String s = "\\<{ int x = 1; {int s = 2;} }\\> x=x";
        Term t = parseTerm(s);
        LOGGER.info("Out: {}", t);
    }

    @Test
    public void test11() throws Exception {
        String s = "\\[{ int x = 2; {String s = \"\\\"}\";} }\\] true";
        Term t = parseTerm(s);
        LOGGER.info("Out: {}", t);
    }


    @Disabled("weigl: #1506")
    @Test
    public void test12() throws Exception {
        String s = "\\<{int i; i=0;}\\> \\<{ while (i>0) ;}\\>true";
        Term t = parseTerm(s);
        LOGGER.info("Out: {}", t);
    }

    @Test
    public void test13() throws Exception {
        Term t1 = parseTerm(
            "\\exists elem x; \\forall list ys; \\forall list xs; ( xs =" + " cons(x,ys))");
        Term t2 = parseTerm(
            "\\exists elem y; \\forall list xs; \\forall list ys; ( ys =" + " cons(y,xs))");
        Term t3 =
            parseTerm("\\exists int_sort bi; (\\<{ int p_x = 1;" + " {int s = 2;} }\\>" + " true ->"
                + "\\<{ int p_x = 1;boolean p_y=2<1;" + " while(p_y){ int s=3 ;} }\\>" + " true)");
        Term t4 =
            parseTerm("\\exists int_sort ci; (\\<{ int p_y = 1;" + " {int s = 2;} }\\>" + " true ->"
                + "\\<{ int p_y = 1;boolean p_x = 2<1;" + "while(p_x){ int s=3 ;} }\\>" + " true)");
        assertTrue(t3.equalsModRenaming(t4), "Terms should be equalModRenaming");
    }

    @Test
    public void test14() throws Exception {
        String s = "\\<{int[] i;i=new int[5];}\\>true";
        Term t = parseTerm(s);
        s = "\\<{int[] i;}\\>\\<{}\\>true";
        t = parseTerm(s);
        LOGGER.info("Out: {}", t);
    }

    @Test
    @Disabled
    public void xtestBindingUpdateTermOldBindingAlternative() throws Exception {
        String s = "\\<{int i,j;}\\> {i:=j} i = j";
        Term t = parseTerm(s);
        assertTrue(t.sub(0).op() instanceof UpdateApplication,
            "expected {i:=j}(i=j) but is ({i:=j}i)=j)");
    }

    @Test
    public void testBindingUpdateTerm() throws Exception {
        String s = "\\forall int j; {globalIntPV:=j} globalIntPV = j";
        String exp = "\\forall int j; ({globalIntPV:=j} globalIntPV) = j";
        Term t = parseTerm(s);
        Term u = parseTerm(exp);
        assertFalse(t.sub(0).op() instanceof UpdateApplication,
            "expected ({globalIntPV:=j}globalIntPV)=j) but is {globalIntPV:=j}(globalIntPV=j)");
    }

    @Test
    public void testBindingUpdateTerm_1() throws Exception {
        assertTermEquals("\\forall int l;  {globalIntPV:=l} false & true",
            "(\\forall int l;  {globalIntPV:=l} false) & true");
    }

    @Test
    public void testBindingUpdateTerm_3() throws Exception {
        assertTermEquals(
            "\\forall int l;  ( \\<  {int globalIntPV=0;} \\>  {globalIntPV:=l} false & true )",
            "\\forall int l;  ( (\\<  {int globalIntPV=0;} \\>  {globalIntPV:=l} false) & true )");
    }

    @Test
    public void testBindingUpdateTerm_4() throws Exception {
        assertTermEquals("! 1=1", "!(1=1)");
    }

    @Test
    public void testBindingUpdateTerm_5() throws Exception {
        assertTermEquals("{globalIntPV:=j} globalIntPV + j", "({globalIntPV:=j} globalIntPV) + j");
    }

    @Test
    public void testBindingUpdateTerm_6() throws Exception {
        assertTermEquals("(int) {\\subst int x; j} j +j", "((int) {\\subst int x; j} j) + j");
    }

    @Test
    public void testBindingUpdateTerm_7() throws Exception {
        assertTermEquals("(int) {\\subst int x; j} j + j", "((int) {\\subst int x; j} j) + j");
    }

    @Test
    public void testBindingUpdateTerm_8() throws Exception {
        assertTermEquals("{\\subst int x; j} (int) j + j", "({\\subst int x; j} (int) j) + j");
    }

    private void assertTermEquals(String actual, String expected) throws Exception {
        Term t = parseTerm(actual);
        Term u = parseTerm(expected);
        LOGGER.debug("Actual: {}", t);
        LOGGER.debug("Expected: {}", u);
        assertEquals(u.toString(), t.toString());
    }


    @Test
    public void testParsingArray() throws Exception {
        String s = "\\forall int[][] i; \\forall int j; i[j][j] = j";
        parseTerm(s);
    }


    @Test
    @Disabled
    public void xtestParsingArrayWithSpaces() throws Exception {
        String s = "\\<{int[][] i; int j;}\\> i[ j ][ j ] = j";
        parseTerm(s);
    }

    @Test
    public void testParsingArrayCombination() throws Exception {
        String s = "\\forall int[][] i; \\forall int j; i [i[i[j][j]][i[j][j]]][i[j][i[j][j]]] = j";
        parseTerm(s);
    }


    @Test
    public void testAmbigiousFuncVarPred() {
        // tests bug id 216
        String s = "\\functions {} \\predicates{mypred(int, int);}"
            + "\n\\problem {\\forall int x; mypred(x, 0)}\n \\proof {\n" + "(branch \"dummy ID\""
            + "(opengoal \"  ==> true  -> true \") ) }";
        try {
            parseProblem(s);
        } catch (Exception re) {
            fail("Fixed bug 216 occured again. The original bug "
                + "was due to ambigious rules using semantic " + "predicates in a 'wrong' way");
        }
    }

    static final String COMPILATION_UNIT = "public class T extends " + "java.lang.Object{ "
        + "private T a;" + "private static T b;" + "T c;" + "static T d;" + "public T e;"
        + "public static T f;" + "protected T g;" + "protected T h;" + "public T query(){} "
        + "public static T staticQ(T p){} " + "public static T staticQ() {}}";


    public Term testParseQueriesAndAttributes(String expr) throws Exception {
        TacletForTests.getJavaInfo().readJavaBlock("{}");
        // r2k.readCompilationUnit(COMPILATION_UNIT);
        return parseTerm("\\forall T t; " + expr);
    }

    @Test
    public void testAttributeOnObject() throws Exception {
        testParseQueriesAndAttributes("t.query()=t");
    }

    @Test
    public void testAttributeWithSpecifiedSortOnObject() throws Exception {
        testParseQueriesAndAttributes("t.(T::query)()=t");
    }

    @Test
    public void testJavaStaticQuery() throws Exception {
        testParseQueriesAndAttributes("T.staticQ()=t");
    }

    @Test
    public void testJavaStaticQueryWithParameter() throws Exception {
        testParseQueriesAndAttributes("T.staticQ(t)=t");
    }

    @Test
    public void testJavaAttributeAccessBoth_1() throws Exception {
        testParseQueriesAndAttributes("T.b=t.(T::a)");
    }

    @Test
    public void testJavaAttributeAccessBoth_2() throws Exception {
        testParseQueriesAndAttributes("T.d=t.(T::c)");
    }

    @Test
    public void testJavaAttributeAccessBoth_3() throws Exception {
        testParseQueriesAndAttributes("t.(T::e)=T.f");
    }

    @Test
    public void testJavaAttributeAccess_4() throws Exception {
        testParseQueriesAndAttributes("t.(T::g)=t.(T::h)");
    }

    @Test
    @Disabled
    public void testJavaQueryAndAttribute_all() throws Exception {
        String all = "\\forall T t;( (t.query()=t & t.(T::query)()=t & T.staticQ()=t "
            + "& T.staticQ(t)=t & T.b=t.(T::a) & T.d=t.(T::c) & t.(T::e)=T.f & t.(T::g)=t.(T::h)))";
        testParseQueriesAndAttributes(all);
    }

    @Test
    public void testProgramVariables() {
        TacletForTests.getJavaInfo().readJavaBlock("{}");
        r2k.readCompilationUnit("public class T0 extends " + "java.lang.Object{} ");
        String s = "\\<{T0 t;}\\> t(1,2) = t()";
        boolean parsed = false;
        try {
            parseTerm(s);
            parsed = true;
        } catch (Exception ignored) {
        }
        assertFalse(parsed, "Program variables should not have arguments");
    }

    @Test
    public void testNegativeLiteralParsing1() throws Exception {
        String s1 = "-1234";
        Term t = parseTerm(s1);
        assertEquals("Z", t.op().name().toString());
        assertEquals("neglit", t.sub(0).op().name().toString());
    }

    @Test
    public void testNegativeLiteralParsing2() throws Exception {
        String s2 = "-(1+1) ";
        Term t = parseTerm(s2);
        assertEquals("neg", t.op().name().toString(), "Failed parsing negative complex term");
    }

    @Test
    public void testNegativeLiteralParsing3() throws Exception {
        String s3 = "\\forall int i; -i = 0 ";
        Term t = parseTerm(s3);
        assertEquals("neg", t.sub(0).sub(0).op().name().toString());
    }

    @Test
    public void testIfThenElse() throws Exception {
        Term t = null, t2 = null;

        String s1 = "\\if (3=4) \\then (1) \\else (2)";
        try {
            t = parseTerm(s1);
        } catch (Exception e) {
            fail();
        }
        assertTrue(
            t.op() == IfThenElse.IF_THEN_ELSE && t.sub(0).equals(parseTerm("3=4"))
                    && t.sub(1).equals(parseTerm("1")) && t.sub(2).equals(parseTerm("2")),
            "Failed parsing integer if-then-else term");

        String s2 = "\\if (3=4 & 1=1) \\then (\\if (3=4) \\then (1) \\else (2)) \\else (2)";
        try {
            t2 = parseTerm(s2);
        } catch (Exception e) {
            fail();
        }
        assertTrue(
            t2.op() == IfThenElse.IF_THEN_ELSE && t2.sub(0).equals(parseTerm("3=4 & 1=1"))
                    && t2.sub(1).equals(t) && t2.sub(2).equals(parseTerm("2")),
            "Failed parsing nested integer if-then-else term");

        String s3 = "\\if (3=4) \\then (1=2) \\else (2=3)";
        try {
            t = parseTerm(s3);
        } catch (Exception e) {
            fail();
        }
        assertTrue(
            t.op() == IfThenElse.IF_THEN_ELSE && t.sub(0).equals(parseTerm("3=4"))
                    && t.sub(1).equals(parseTerm("1=2")) && t.sub(2).equals(parseTerm("2=3")),
            "Failed parsing propositional if-then-else term");

    }

    @Test
    public void testInfix1() throws Exception {
        assertEquals(parseTerm("aa + bb"), parseTerm("add(aa,bb)"), "infix1");
    }

    @Test
    public void testInfix2() throws Exception {
        assertEquals(parseTerm("aa + bb*cc"), parseTerm("add(aa,mul(bb,cc))"), "infix2");
    }

    @Test
    public void testInfix3() throws Exception {
        assertEquals(parseTerm("aa + bb*cc < 123 + -90"),
            parseTerm("lt(add(aa,mul(bb,cc)),add(123,-90))"), "infix3");
    }

    @Test
    public void testInfix4() throws Exception {
        // Test: Multiplication/Modulo/Div should be left associative
        Term termInfix = parseTerm("aa%bb*cc < -123");
        Term termPrefix = parseTerm("lt(mul(mod(aa,bb),cc),-123)");
        assertEqualsIgnoreWhitespaces("lt(mul(mod(aa,bb),cc),Z(neglit(3(2(1(#))))))",
            termInfix.toString());
        assertEqualsIgnoreWhitespaces("lt(mul(mod(aa,bb),cc),Z(neglit(3(2(1(#))))))",
            termPrefix.toString());
        assertEquals(termInfix, termPrefix);
    }

    @Test
    public void testCast() throws Exception {
        assertEquals(parseTerm("((int)3)+2"), parseTerm("(int)3+2"), "cast stronger than plus");
    }

    // public void testParseTermsWithLabels() {
    // // First register the labels ...
    // TermLabels.registerSymbolicExecutionTermLabels(serv.getProfile().getTermLabelManager());
    //
    // Term t = parseTerm("(3 + 2)<<" + SimpleTermLabel.LOOP_BODY_LABEL_NAME + ">>");
    // assertTrue(t.hasLabels());
    // t = parseTerm("3 + 2<<" + SimpleTermLabel.LOOP_BODY_LABEL_NAME + ">>");
    // assertFalse(t.hasLabels());
    // assertTrue(t.sub(1).hasLabels());
    //
    // try {
    // t = parseTerm("(3 + 2)<<unknownLabel>>");
    // fail("Term " + t + " should not have been parsed");
    // } catch(Exception ex) {
    // // expected
    // }
    // }
}
