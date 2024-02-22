/*
 * Copyright (C) 2010 Universitaet Karlsruhe, Germany
 *    written by Mattias Ulbrich
 *
 * The system is protected by the GNU General Public License.
 * See LICENSE.TXT for details.
 */
package edu.kit.kastel.formal.mixfix;

import org.junit.Before;
import org.junit.Test;

import java.util.Arrays;
import static org.junit.Assert.*;

/**
 * Test cases for the {@link MixFixParser}.
 */
public class TestMixFixParser {

    private MixFixParser<String, String> parser;
    private MixFixRuleCollection<String, String> coll;

    @Before
    public void setUp() throws Exception {
        coll = new MixFixRuleCollection<String, String>();
        parser = new MixFixParser<String,String>(coll);
    }

    private String parse(String arg) throws MixFixException {
        String[] arr = arg.split(" ");
        String result = parser.parseExpression(Arrays.asList(arr));
        System.out.println(arg + " ==> " + result);
        return result;
    }

    public static void addComplexGrammar(MixFixRuleCollection<String, String> coll) {
        coll.addRule(new IdentifierRule());
        coll.addRule(new NaturalNumberRule());
        coll.addRule(new SyntaxRule("plus", "_ + _", 10, 10));
        coll.addRule(new SyntaxRule("subs", "_ - _", 10, 10));
        coll.addRule(new SyntaxRule("minus", "- _", 100, 100));
        coll.addRule(new SyntaxRule("mult", "_ * _", 20, 20));
        coll.addRule(new SyntaxRule("exp", "_ ^ _", 30, 28));
        coll.addRule(new SyntaxRule("paren", "( _ )", 100, 100));

        coll.addRule(new SyntaxRule("update", "{ _ := _ } _", 100, 100));
        coll.addRule(new SyntaxRule("setex", "{ _ . _ | _ }", 100, 100));
        coll.addRule(new SyntaxRule("setex2", "{ _ | _ } ", 100, 100));
        coll.addRule(new SyntaxRule("shannon", "_ ? _ : _ ", 5, 5));

        coll.addRule(new SyntaxRule("heap", "_ . _ @ _", 30, 30));

        coll.addRule(new SyntaxRule("fcall", " f ( _ )", 30, 30));
    }

    @Test
    public void testPrecedences() throws Exception {
        coll.addRule(new IdentifierRule());
        coll.addRule(new SyntaxRule("plus", "_ + _", 10, 10));
        coll.addRule(new SyntaxRule("mult", "_ * _", 20, 20));

        assertEquals("plus[a,b]", parse("a + b"));
        assertEquals("plus[a,mult[b,c]]", parse("a + b * c"));
        assertEquals("plus[mult[a,b],c]", parse("a * b + c"));
        assertEquals("mult[mult[a,b],c]", parse("a * b * c"));
    }

    @Test
    public void testComplexGrammar() throws Exception {
        try {
            addComplexGrammar(coll);

            assertEquals("plus[1,2]", parse("1 + 2"));
            assertEquals("plus[7,mult[5,2]]", parse("7 + 5 * 2"));
            assertEquals("plus[mult[7,5],2]", parse("7 * 5 + 2"));
            assertEquals("mult[paren[plus[7,5]],2]", parse("( 7 + 5 ) * 2"));
            assertEquals("plus[update[a,5,b],a]", parse("{ a := 5 } b + a"));
            assertEquals("setex[a,subs[a,0],plus[a,5]]", parse("{ a . a - 0 | a + 5 }"));
            assertEquals("shannon[plus[a,b],plus[c,d],plus[e,f]]", parse("a + b ? c + d : e + f"));
            assertEquals("heap[paren[heap[o,f,h]],g,i]", parse("( o . f @ h ) . g @ i"));
            assertEquals("heap[heap[o,f,h],g,i]", parse("o . f @ h . g @ i"));
            assertEquals("plus[plus[1,1],1]", parse("1 + 1 + 1"));
            assertEquals("exp[1,exp[1,1]]", parse("1 ^ 1 ^ 1"));
            assertEquals("plus[a,mult[exp[b,c],d]]", parse("a + b ^ c * d"));
            assertEquals("plus[mult[a,exp[b,c]],d]", parse("a * b ^ c + d"));
            assertEquals("plus[a,mult[b,exp[c,d]]]", parse("a + b * c ^ d"));
            assertEquals("mult[exp[a,b],c]", parse("a ^ b * c"));
            assertEquals("mult[exp[a,minus[b]],c]", parse("a ^ - b * c"));
        } catch (MixFixException mfe) {
            System.err.println(mfe.getToken());
            throw mfe;
        }
    }

    @Test
    public void testDevious() throws Exception {
        coll.addRule(new IdentifierRule());
        coll.addRule(new SyntaxRule("low", "_ + _ LOW", 10, 10));
        coll.addRule(new SyntaxRule("mult", "_ * _", 20, 20));
        coll.addRule(new SyntaxRule("high", "_ + _ HIGH", 40, 40));
        coll.addRule(new SyntaxRule("suffix", "_ +", 30, 1000));

        assertEquals("low[a,b]", parse("a + b LOW"));
        assertEquals("mult[a,high[b,c]]", parse("a * b + c HIGH"));
        assertEquals("low[mult[a,b],c]", parse("a * b + c LOW"));
        assertEquals("suffix[a]", parse("a +"));
        assertEquals("mult[a,suffix[b]]", parse("a * b +"));

        assertEquals("mult[high[suffix[b],c],c]", parse("b + + c HIGH * c"));
    }

    /*
     * What if an inner token is the same as the beginning (led) token of an
     * outer sequence?
     *
     * This is ambiguous:
     *   pre[b,inf[c,d]] and pre[inf[b,c],d] are both valid parse trees
     */
    @Test
    public void testInnerOuter() throws Exception {
        coll.addRule(new IdentifierRule());
        coll.addRule(new SyntaxRule("pre", "! _ : _ ", 5, 5));
        coll.addRule(new SyntaxRule("inf", "_ : _ ", 10, 10));

        try {
            parse("! b : c : d");
            fail("Grammar is ambiguous, should be noticed");
        } catch(MixFixException ex) {
        }
    }

    /*
     * This is ambiguous:
     *   pre[inf[b,c], d] and inf[pre[b,c],d] are both valid parse trees
     */
    @Test
    public void testInnerOuter2() throws Exception {
        coll.addRule(new IdentifierRule());
        coll.addRule(new SyntaxRule("pre", "! _ : _ ", 50, 50));
        coll.addRule(new SyntaxRule("inf", "_ : _ ", 10, 10));

        try {
            parse("! b : c : d");
            fail("Grammar is ambiguous, should be noticed");
        } catch(MixFixException ex) {
        }
    }

    @Test
    public void testInnerBinding() throws Exception {
        coll.addRule(new IdentifierRule());
        coll.addRule(new SyntaxRule("p", "_ + _", 20, 20));
        coll.addRule(new SyntaxRule("s", "_ | _ | _", 100, 100));

        assertEquals("p[p[a,s[b,p[c,d],e]],f]", parse("a + b | c + d | e + f"));
    }

    @Test
    public void testAmbiguous() throws Exception {
        coll.addRule(new IdentifierRule());
        coll.addRule(new SyntaxRule("p", "_ + _", 20, 18));

        assertEquals("p[a,p[b,c]]", parse("a + b + c"));
    }

    @Test
    public void testFunctions() throws Exception {
        coll.addRule(new IdentifierRule());
        coll.addRule(new SyntaxRule("funct_app", "F ( _ )", 50, 50));
        coll.addRule(new SyntaxRule("paren", "( _ )", 50, 50));
        coll.addRule(new SyntaxRule("prefix_F", "F _", 50, 50));

        try {
            parse("F ( x )");
            fail("Grammar is ambiguous, should be noticed");
        } catch(MixFixException ex) {
        }
    }

    @Test
    public void testContinuation() throws Exception {
        coll.addRule(new IdentifierRule());
        coll.addRule(new SyntaxRule("eq", "_ = _", 50, 50));
        coll.addRule(new SyntaxRule("not", "! _", 45, 45));
        coll.addRule(new SyntaxRule("anot", "_ !! _", 100, 45));

        assertEquals("eq[a,anot[x,eq[a,a]]]", parse("a = x !! a = a"));
        assertEquals("eq[a,not[eq[a,a]]]", parse("a = ! a = a"));
    }

    @Test
    public void testSequenceParse() throws Exception {
        coll.addRule(new IdentifierRule());
        SyntaxRule plusRule = new SyntaxRule("plus", "_ + _", 10, 10);
        coll.addRule(plusRule);
        coll.addRule(new SyntaxRule("mult", "_ * _", 20, 20));

        ParseContext<String, String> pc =
                new ParseContext<String, String>(parser, Arrays.asList("a + b * c".split(" ")))
                .consumeToken().setResult("a");

        ADTList<ParseContext<String, String>> result = plusRule.parse(pc, 0);
        assertEquals("ParseContext [curPos=5, maxBinding=10, result=plus[a,mult[b,c]]]",
                result.hd().toString());
        assertEquals("ParseContext [curPos=3, maxBinding=10, result=plus[a,b]]",
                result.tl().hd().toString());
    }

    @Test
    public void testIfThenElse() throws Exception {
        coll.addRule(new IdentifierRule());
        coll.addRule(new SyntaxRule("ite", "if _ then _ else _", 0, 0));
        coll.addRule(new SyntaxRule("wite", "weakif _ then _ else _", 0, 40));
        coll.addRule(new SyntaxRule("plus", "_ + _", 20, 20));

        assertEquals("ite[plus[a,b],plus[a,b],plus[a,b]]",
                parse("if a + b then a + b else a + b"));

        assertEquals("plus[wite[plus[a,b],plus[a,b],a],b]",
                parse("weakif a + b then a + b else a + b"));
    }

    @Test
    public void testVeryLargeGrammar() throws Exception {
        for (int i = 0; i < 100; i++) {
            coll.addRule(new SyntaxRule("lit-" + i, ""+i, 0, 0));
            coll.addRule(new SyntaxRule("no-"  + i, "_ -" + i + "- _", i, i));
        }

        assertEquals("no-22[no-22[lit-1[],no-33[lit-2[],lit-3[]]],lit-4[]]",
                parse("1 -22- 2 -33- 3 -22- 4"));
        assertEquals("no-11[no-22[no-22[lit-1[],no-33[lit-2[],lit-3[]]]," +
                "lit-4[]],no-77[no-99[lit-5[],lit-5[]],lit-1[]]]",
                parse("1 -22- 2 -33- 3 -22- 4 -11- 5 -99- 5 -77- 1"));
    }

    // was a bug
    @Test
    public void testLongerExpression() throws Exception {
        coll.addRule(new IdentifierRule());
        coll.addRule(new SyntaxRule("plus", "_ + _", 10, 10));
        coll.addRule(new SyntaxRule("mult", "_ * _", 20, 20));

        assertEquals("plus[plus[plus[plus[plus[a,mult[b,c]],d],e],f],g]",
                parse("a + b * c + d + e + f + g"));
        assertEquals("plus[plus[plus[plus[plus[a,b],mult[c,d]],e],f],g]",
                parse("a + b + c * d + e + f + g"));
    }
}