/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import java.io.IOException;
import javax.annotation.Nonnull;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Operator;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static org.junit.jupiter.api.Assertions.*;

/**
 * Parser tests for heap terms.
 *
 * @author Kai Wallisch <kai.wallisch@ira.uka.de>
 */
public class TestTermParserHeap extends AbstractTestTermParser {
    private static final Logger LOGGER = LoggerFactory.getLogger(TestTermParserHeap.class);
    private Term h, a, f, next;

    @BeforeEach
    public void setUp() throws Exception {
        parseDecls("\\programVariables {Heap h, h2;}");
        parseDecls("\\programVariables {int i;}");
        parseDecls("\\programVariables {testTermParserHeap.A a;}");
        parseDecls("\\programVariables {testTermParserHeap.A1 a1;}");
        parseDecls("\\programVariables {testTermParserHeap.A[] array;}");

        assertNotNull(nss.programVariables().lookup("a"));
        assertNotNull(nss.programVariables().lookup("a1"));
        assertNotNull(nss.programVariables().lookup("array"));
        assertNotNull(nss.programVariables().lookup("h"));
        assertNotNull(nss.programVariables().lookup("h2"));

        this.h = parseTerm("h");
        this.a = parseTerm("a");
        next = parseTerm("testTermParserHeap.A::$next");
        f = parseTerm("testTermParserHeap.A::$f");
    }

    private Term getSelectTerm(String sort, Term heap, Term object, Term field) {
        Operator op = lookup_func(sort + "::select");
        Term[] params = new Term[] { heap, object, field };
        return tf.createTerm(op, params);
    }

    @Test
    public void testAllFieldsSelector() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("a.*", "allFields(a)");
    }

    @Test
    public void testLocationSets() throws Exception {
        String pp = "{(a, testTermParserHeap.A::$f)}";
        String verbose = "singleton(a,testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(pp, verbose);

        comparePrettySyntaxAgainstVerboseSyntax("{}", "empty");

        pp = "{(a, testTermParserHeap.A::$f), (a, testTermParserHeap.A::$f), (a, testTermParserHeap.A::$f)}";
        Term expected = parseTerm(
            "union(union(singleton(a,testTermParserHeap.A::$f),singleton(a,testTermParserHeap.A::$f)),singleton(a,testTermParserHeap.A::$f))");
        verifyParsing(expected, pp);
    }

    @Test
    public void testParsePrettyPrintedSelect() throws Exception {
        String prettySyntax = "a.f";
        String verboseSyntax = "int::select(heap, a, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);

        prettySyntax = "a1.f";
        verboseSyntax = "int::select(heap, a1, testTermParserHeap.A1::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);

        prettySyntax = "a1.(testTermParserHeap.A::f)";
        verboseSyntax = "int::select(heap, a1, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);
    }

    @Test
    public void testBracketHeapUpdate() throws Exception {
        String complicatedHeapPretty =
            "heap[a.f := 4][create(a)][memset({}, 1)][anon(allLocs, heap)]";
        String complicatedHeapVerbose =
            "anon(memset(create(store(heap, a, testTermParserHeap.A::$f, 4), a), empty, 1), allLocs, heap)";
        comparePrettySyntaxAgainstVerboseSyntax(complicatedHeapPretty, complicatedHeapVerbose);

        String prettySyntax = "a.f@h[anon({}, h2)]";
        String verboseSyntax = "int::select(anon(h, empty, h2), a, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);

        /*
         * Testing a more complicated term in which bracket syntax is applied before and
         * after @-Operator.
         */
        prettySyntax = "a.next.next.array[i]@" + complicatedHeapPretty;
        verboseSyntax = "int::select(" + complicatedHeapVerbose + ", " + "int[]::select("
            + complicatedHeapVerbose + ", " + "testTermParserHeap.A::select("
            + complicatedHeapVerbose + ", " + "testTermParserHeap.A::select("
            + complicatedHeapVerbose + ", " + " a, testTermParserHeap.A::$next)"
            + ", testTermParserHeap.A::$next)" + ", testTermParserHeap.A::$array)" + ", arr(i))";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);
    }

    /*
     * The @-Operator can be used to specify the heap, which belongs to a field access. That
     * operator is tested in the method below.
     */
    @Test
    public void testAtOperator_1() throws Exception {
        String prettySyntax, verboseSyntax;

        prettySyntax = "a.f@h";
        verboseSyntax = "int::select(h, a, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);
    }

    @Test
    public void testAtOperator_2() throws Exception {
        String prettySyntax = "a1.f@h";
        String verboseSyntax = "int::select(h, a1, testTermParserHeap.A1::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);
    }

    @Test
    public void testAtOperator_3() throws Exception {
        String prettySyntax = "a1.(testTermParserHeap.A::f)@h";
        String verboseSyntax = "int::select(h, a1, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);
    }

    @Test
    public void testAtOperator_4() throws Exception {
        Term expectedParseResult = getSelectTerm("testTermParserHeap.A", h, a, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("int", h, expectedParseResult, f);
        compareStringRepresentationAgainstTermRepresentation("a.next.next.next.f@h",
            expectedParseResult, "(a.next).next.next.f@h", "(a.next.next).next.f@h",
            "(a.next.next.next).f@h");
    }

    @Test
    public void testAtOperator_5() throws Exception {
        Term h2 = parseTerm("h2");
        Term expectedParseResult = getSelectTerm("testTermParserHeap.A", h2, a, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h2, expectedParseResult, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("int", h, expectedParseResult, f);
        compareStringRepresentationAgainstTermRepresentation("(a.next.next@h2).next.f@h",
            expectedParseResult);
    }

    @Test
    public void testAtOperator_6() throws Exception {
        Term aDotF = getSelectTerm("int", tb.getBaseHeap(), a, f); // a.f
        Term aDotArray = getSelectTerm("int[]", h, a, parseTerm("testTermParserHeap.A::$array")); // a.array
        Term expectedParseResult = getSelectTerm("int", h, aDotArray, tb.arr(aDotF));
        compareStringRepresentationAgainstTermRepresentation("a.array[a.f]@h", expectedParseResult);
    }

    @Test
    public void testAtOperator_7() throws Exception {
        Term aDotF = getSelectTerm("int", h, a, f); // a.f
        Term aDotArray =
            getSelectTerm("int[]", tb.getBaseHeap(), a, parseTerm("testTermParserHeap.A::$array")); // a.array
        Term expectedParseResult = getSelectTerm("int", tb.getBaseHeap(), aDotArray, tb.arr(aDotF));
        compareStringRepresentationAgainstTermRepresentation("a.array[a.f@h]", expectedParseResult);

    }

    @Test
    public void testAtOperator_8() throws Exception {
        Term expectedParseResult = getSelectTerm("testTermParserHeap.A", tb.getBaseHeap(), a, next);
        expectedParseResult = getSelectTerm("testTermParserHeap.A", h, expectedParseResult, next);
        expectedParseResult = getSelectTerm("int", h, expectedParseResult, f);
        compareStringRepresentationAgainstTermRepresentation("(a.next@heap).next.f@h",
            expectedParseResult, "((a.next@heap)).next.f@h");
    }

    @Test
    public void testBugResettingCounter() throws Exception {
        String prettySyntax = "a.f = a.f@h";
        String verboseSyntax =
            "int::select(heap, a, testTermParserHeap.A::$f) = int::select(h, a, testTermParserHeap.A::$f)";
        comparePrettySyntaxAgainstVerboseSyntax(prettySyntax, verboseSyntax);
    }

    /*
     * In this test, the @-Operator is applied on a non-select term. This should cause a parser
     * error. This test verifies that the correct Exception is thrown.
     */
    @Test
    public void testVerifyExceptionIfAtOperatorNotPreceededBySelectTerm() {
        try {
            @Nonnull
            Term t = io.parseExpression("(a.f + a.f)@h2");
            LOGGER.info("Out: {}", t);
            fail();
        } catch (Exception e) {
            // assertTrue(e.getMessage().contains(ExpressionBuilder.NO_HEAP_EXPRESSION_BEFORE_AT_EXCEPTION_MESSAGE));
        }
    }

    // this was a bug in the pretty printing
    @Test
    // @Ignore(value="weigl: This test is not comprehensible anymore.")
    public void testUnknownConstant() throws Exception {
        parseDecls("\\functions { \\unique Field unkonwn.Clazz::$unknownField; }");
        String string = "int::select(heap,a,unkonwn.Clazz::$unknownField)";
        comparePrettyPrintAgainstToString(string, string);
    }

    @Test
    public void testQuantifiedSelect() throws Exception {
        String quantification = "\\forall java.lang.Object o; \\forall Field f; o.f = 1";
        String expectedToString =
            "all{o:java.lang.Object}(all{f:Field}(equals(any::select(heap,o,f),Z(1(#)))))";
        comparePrettyPrintAgainstToString(quantification, expectedToString);

        quantification = "\\forall Field f; a.f = any::select(heap, a, f)";
        expectedToString =
            "all{f:Field}(equals(int::select(heap,a,testTermParserHeap.A::$f),any::select(heap,a,f)))";
        comparePrettyPrintAgainstToString(quantification, expectedToString);

    }

    private void comparePrettyPrintAgainstToString(String quantification, String expectedToString)
            throws Exception {
        Term t = parseTerm(quantification);
        assertEquals(expectedToString, t.toString());
        assertEqualsIgnoreWhitespaces(quantification, printTerm(t));
    }

    @Test
    public void testGenericObjectProperties() throws Exception {
        // test pretty syntax
        comparePrettySyntaxAgainstVerboseSyntax("a.<created>",
            "boolean::select(heap,a,java.lang.Object::<created>)");
        comparePrettySyntaxAgainstVerboseSyntax("a.<initialized>",
            "boolean::select(heap,a,java.lang.Object::<initialized>)");
        comparePrettySyntaxAgainstVerboseSyntax("a.<transient>",
            "int::select(heap,a,java.lang.Object::<transient>)");

        // test fallback mode in case non-default select-type is used
        parseAndPrint("int::select(heap,a,java.lang.Object::<created>)");

    }

    @Test
    public void testQueryBasic_1() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("a.query(i)",
            "testTermParserHeap.A::query(heap, a, i)");
    }

    @Test
    public void testQueryBasic_2() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("a.query(i)@h",
            "testTermParserHeap.A::query(h, a, i)");
    }

    @Test
    public void testQueryBasic_3() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("a.query(a.f)@h",
            "testTermParserHeap.A::query(h, a, "
                + "int::select(heap, a, testTermParserHeap.A::$f))");

    }

    @Test
    public void testQueryBasic_4() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("a.next.query(a.f)@h",
            "testTermParserHeap.A::query(h, "
                + "testTermParserHeap.A::select(h, a, testTermParserHeap.A::$next),  "
                + "int::select(heap, a, testTermParserHeap.A::$f))");

    }

    @Test
    public void testQueryBasic_5() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("a.getNext().getNext()@h",
            "testTermParserHeap.A::getNext(h, " + "testTermParserHeap.A::getNext(h, a))");

    }

    @Test
    public void testQueryBasic_6() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("a.getNext().next@h",
            "testTermParserHeap.A::select(h, "
                + "testTermParserHeap.A::getNext(h, a), testTermParserHeap.A::$next)");

    }

    @Test
    public void testQueryBasic_7() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("(a.getNext()@h2).next@h",
            "testTermParserHeap.A::select(h, testTermParserHeap.A::getNext(h2, a), testTermParserHeap.A::$next)");

    }

    @Test
    public void testQueryBasic_8() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("(a.getNext()@heap).next@h",
            "testTermParserHeap.A::select(h, "
                + "testTermParserHeap.A::getNext(heap, a), testTermParserHeap.A::$next)");

    }

    @Test
    public void testQueryBasic_9() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("(a.next@heap).getNext()@h",
            "testTermParserHeap.A::getNext(h, "
                + "testTermParserHeap.A::select(heap, a, testTermParserHeap.A::$next))");

    }

    @Test
    public void testQueryBasic_10() throws Exception {
        // test a query whose argument is an array variable
        comparePrettySyntaxAgainstVerboseSyntax("a1.arrayQuery(array)",
            "testTermParserHeap.A::arrayQuery(heap,a1,array)");

    }

    @Test
    public void testQueryBasic_11() throws Exception {
        // test a query on an array element
        comparePrettySyntaxAgainstVerboseSyntax("array[i].arrayQuery(array)",
            "testTermParserHeap.A::arrayQuery(heap,testTermParserHeap.A::select(heap,array,arr(i)),array)");
    }

    @Test
    public void testQueryInheritance_1() throws Exception {
        comparePrettySyntaxAgainstVerboseSyntax("a.query(i)",
            "testTermParserHeap.A::query(heap, a, i)", "a.(testTermParserHeap.A::query)(i)");

    }

    @Test
    public void testQueryInheritance_2() throws Exception {
        // test public query defined in superclass, which is not overridden
        comparePrettySyntaxAgainstVerboseSyntax("a1.query(i)",
            "testTermParserHeap.A::query(heap, a1, i)", "a1.(testTermParserHeap.A::query)(i)");

    }

    @Test
    public void testQueryInheritance_3() throws Exception {
        // test redefined (private) query
        comparePrettySyntaxAgainstVerboseSyntax("a1.queryRedefined()",
            "testTermParserHeap.A1::queryRedefined(heap, a1)",
            "a1.(testTermParserHeap.A1::queryRedefined)()");

    }

    @Test
    public void testQueryInheritance_4() throws Exception {
        // test redefined (private) query - explicitly reference query from superclass
        comparePrettySyntaxAgainstVerboseSyntax("a1.(testTermParserHeap.A::queryRedefined)()",
            "testTermParserHeap.A::queryRedefined(heap, a1)");

    }

    @Test
    public void testQueryInheritance_5() throws Exception {
        // test overridden (public) query
        comparePrettySyntaxAgainstVerboseSyntax("a1.queryOverridden()",
            "testTermParserHeap.A::queryOverridden(heap, a1)");

    }

    @Test
    public void testQueryInheritance_6() throws Exception {
        // test whether toString() query inherited from java.lang.Object gets parsed correctly
        comparePrettySyntaxAgainstVerboseSyntax("a1.toString()@h",
            "java.lang.Object::toString(h, a1)");

    }

    @Test
    public void testQueryInheritance_7() throws Exception {
        // test overridden query with explicitly specified classname
        comparePrettySyntaxAgainstVerboseSyntax("a1.(testTermParserHeap.A1::queryOverridden)()",
            "testTermParserHeap.A1::queryOverridden(heap,a1)");

    }

    @Test
    public void testQueryInheritance_8() throws Exception {
        // test overridden query with explicitly specified classname in combination with a
        // non-standard heap
        comparePrettySyntaxAgainstVerboseSyntax("a1.(testTermParserHeap.A1::queryOverridden)()@h",
            "testTermParserHeap.A1::queryOverridden(h,a1)");

    }

    @Test
    public void testQueryInheritance_9() throws Exception {
        // test an overridden query with several arguments
        comparePrettySyntaxAgainstVerboseSyntax("a1.queryOverriddenWithArguments(i,a,a1)@h",
            "testTermParserHeap.A::queryOverriddenWithArguments(h,a1,i,a,a1)");
    }

    /*
     * Test pretty-printing on static fields and methods.
     */
    @Test
    public void testAccessStaticMembers() throws Exception {
        // static field access
        comparePrettySyntaxAgainstVerboseSyntax("testTermParserHeap.A.staticField",
            "int::select(heap, null, testTermParserHeap.A::$staticField)");

        // static method access
        comparePrettySyntaxAgainstVerboseSyntax("testTermParserHeap.A.staticMethod()",
            "testTermParserHeap.A::staticMethod(heap)", "a.staticMethod()", "a1.staticMethod()");

        // static array access
        comparePrettySyntaxAgainstVerboseSyntax("testTermParserHeap.A.staticArray[0]",
            "int::select(heap,int[]::select(heap,null,testTermParserHeap.A::$staticArray),arr(Z(0(#))))");
    }

    /*
     * Test parsing and printing of store-terms.
     */
    @Test
    public void testStore() throws Exception {
        String pretty, verbose;

        // non-static non-hidden field
        pretty = "heap[a.f := null]";
        verbose = "store(heap, a, testTermParserHeap.A::$f, null)";
        comparePrettySyntaxAgainstVerboseSyntax(pretty, verbose);

        // non-static hidden field
        pretty = "heap[a.(testTermParserHeap.A1::f) := null]";
        verbose = "store(heap, a, testTermParserHeap.A1::$f, null)";
        comparePrettySyntaxAgainstVerboseSyntax(pretty, verbose);

        // static field
        pretty = "heap[testTermParserHeap.A.staticArray := null]";
        verbose = "store(heap, null, testTermParserHeap.A::$staticArray, null)";
        comparePrettySyntaxAgainstVerboseSyntax(pretty, verbose);

        // element of static array
        pretty = "heap[testTermParserHeap.A.staticArray[i] := i]";
        verbose =
            "store(heap, int[]::select(heap,null,testTermParserHeap.A::$staticArray), arr(i), i)";
        comparePrettySyntaxAgainstVerboseSyntax(pretty, verbose);

        // object property
        pretty = "heap[create(a)][a.<initialized> := FALSE]";
        verbose = "store(create(heap,a),a,java.lang.Object::<initialized>,FALSE)";
        comparePrettySyntaxAgainstVerboseSyntax(pretty, verbose);

    }

    /**
     * Test whether printing is inverse to parsing on a specific {@link String}.
     *
     * @param s Pretty-printed String representation of a term.
     * @throws IOException
     */
    private void parseAndPrint(String s) throws Exception {
        Term t = parseTerm(s);
        String printedSyntax = printTerm(t);
        assertEqualsIgnoreWhitespaces(s, printedSyntax);
    }

}
