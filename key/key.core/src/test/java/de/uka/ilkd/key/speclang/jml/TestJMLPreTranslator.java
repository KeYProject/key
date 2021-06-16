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

package de.uka.ilkd.key.speclang.jml;

import de.uka.ilkd.key.speclang.njml.JmlFacade;
import de.uka.ilkd.key.speclang.njml.JmlIO;
import de.uka.ilkd.key.speclang.njml.JmlLexer;
import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import junit.framework.TestCase;
import org.antlr.v4.runtime.Token;
import org.junit.Ignore;
import org.junit.Test;
import org.key_project.util.collection.ImmutableList;

import static de.uka.ilkd.key.speclang.njml.JmlLexer.*;
import static junit.framework.TestCase.assertEquals;
import static junit.framework.TestCase.assertSame;
import static org.junit.Assert.*;


public class TestJMLPreTranslator {
    private ImmutableList<TextualJMLConstruct> parseMethodSpec(String ms) {
        return new JmlIO().parseClassLevel(ms);
    }

    //region lexing
    @Test
    public void testLexer1() {
        String in = "/*@ normal_behavior\n"
                + "     requires true;\n"
                + "  */";
        lex(in, JML_ML_START, WS, NORMAL_BEHAVIOR, WS, REQUIRES);
    }

    @Test
    public void testLexer2() {
        lex("ensures //-key@ this should be ignored\n" +
                        "true;",
                ENSURES, WS, COMMENT, WS, TRUE, SEMI_TOPLEVEL, EOF);
    }

    @Test
    public void testLexer3() {
        lex("ensures      /*-key@ this should be ignored */ true;",
                ENSURES, WS, COMMENT, WS, TRUE, SEMI_TOPLEVEL, EOF);
    }

    @Test
    public void testLexer4() {
        lex("/*-openjml@ ensures true; */",
                JML_ML_START, WS, ENSURES, WS, TRUE, SEMI_TOPLEVEL, WS, JML_ML_END, EOF);
    }

    @Test
    public void testLexer5() {
        lex("/*@ pure */ /*@ ensures true;",
                JML_ML_START, WS, PURE, WS, JML_ML_END, WS,
                JML_ML_START, WS, ENSURES, WS, TRUE, SEMI_TOPLEVEL, EOF);
    }

    @Test
    public void testLexer6() {
        lex("//@ normal_behaviour\n"
                        + "//@  ensures false\n"
                        + "//@          || true;\n"
                        + "//@  assignable \\nothing;\n"
                        + "//@ also exceptional_behaviour\n"
                        + "//@  requires o == null;\n"
                        + "//@  signals Exception;\n",
                JML_SL_START, WS, NORMAL_BEHAVIOR, WS, JML_SL_START, WS, ENSURES, WS);
    }

    @Test
    public void testLexer7() {
        lex("//+ESC@ special comment for ESC",
                SL_COMMENT);
    }

    @Test
    public void testLexer8() {
        lex("//+ESC+key@ behaviour",
                JML_SL_START, WS, BEHAVIOR);
    }

    @Test
    public void testLexer9() {
        lex("//+ESC+key-key@ behaviour",
                SL_COMMENT);
    }

    @Test
    public void testLexer10() {
        lex("//-@ behaviour", SL_COMMENT);
        lex("//+key+@ behaviour", SL_COMMENT);
        lex("//key@ behaviour", SL_COMMENT);
    }

    private void lex(String in, int... expected) {
        JmlLexer lexer = JmlFacade.createLexer(in);
        Token t;
        int idx = 0;
        do {
            t = lexer.nextToken();
            System.out.printf("%s\n", t);
            if (idx < expected.length) {
                assertEquals(
                        String.format("Token wanted '%s', but got '%s'. ",
                                lexer.getVocabulary().getDisplayName(expected[idx]),
                                lexer.getVocabulary().getDisplayName(t.getType())),
                        expected[idx++], t.getType());
            }
        } while (t.getType() != -1);
    }
    //endregion

    @Test
    public void testSimpleSpec() {
        ImmutableList<TextualJMLConstruct> constructs = parseMethodSpec(
                "/*@ normal_behavior\n"
                        + "     requires true;\n"
                        + "  */");

        assertNotNull(constructs);
        assertEquals(1, constructs.size());
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase = (TextualJMLSpecCase) constructs.head();

        TestCase.assertSame(specCase.getBehavior(), Behavior.NORMAL_BEHAVIOR);
        assertEquals(1, specCase.getRequires().size());
        assertEquals(0, specCase.getAssignable().size());
        assertEquals(0, specCase.getEnsures().size());
        assertEquals(0, specCase.getSignals().size());
        assertEquals(0, specCase.getSignalsOnly().size());
        assertEquals("requirestrue;", specCase.getRequires().head().first.getText().trim());
    }


    @Test
    public void testComplexSpec() {
        ImmutableList<TextualJMLConstruct> constructs
                = parseMethodSpec("/*@ behaviour\n"
                + "  @  requires true;\n"
                + "  @  requires a!=null && (\\forall int i; 0 <= i && i <= 2; \\dl_f(i) );\n"
                + "  @  ensures false;\n"
                + "  @  signals (Exception) e;\n"
                + "  @  signals_only onlythis;\n"
                + "  @  assignable \\nothing;\n"
                + "  @*/");

        assertNotNull(constructs);
        assertEquals(1, constructs.size());
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase = (TextualJMLSpecCase) constructs.head();

        assertSame(specCase.getBehavior(), Behavior.BEHAVIOR);
        assertEquals(2, specCase.getRequires().size());
        assertEquals(1, specCase.getAssignable().size());
        assertEquals(1, specCase.getEnsures().size());
        assertEquals(1, specCase.getSignals().size());
        assertEquals(1, specCase.getSignalsOnly().size());

        System.out.println(specCase);

        assertEquals("ensuresfalse;", specCase.getEnsures().head().first.getText().trim());
        assertEquals("assignable\\nothing;", specCase.getAssignable().head().first.getText().trim());
        assertEquals("signals(Exception)e;", specCase.getSignals().head().first.getText().trim());
        assertEquals("signals_onlyonlythis;", specCase.getSignalsOnly().head().first.getText().trim());
        assertEquals("requirestrue;", specCase.getRequires().head().first.getText().trim());
    }


    @Test
    public void testMultipleSpecs() {
        ImmutableList<TextualJMLConstruct> constructs
                = parseMethodSpec("//@ normal_behaviour\n"
                + "//@  ensures false\n"
                + "//@          || true;\n"
                + "//@  assignable \\nothing;\n"
                + "//@ also exceptional_behaviour\n"
                + "//@  requires o == null;\n"
                + "//@  signals (Exception) e;\n");

        assertNotNull(constructs);
        assertEquals(2, constructs.size());
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        assertTrue(constructs.tail().head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase1 = (TextualJMLSpecCase) constructs.head();
        TextualJMLSpecCase specCase2 = (TextualJMLSpecCase) constructs.tail().head();

        assertSame(specCase1.getBehavior(), Behavior.NORMAL_BEHAVIOR);
        assertEquals(0, specCase1.getRequires().size());
        assertEquals(1, specCase1.getAssignable().size());
        assertEquals(1, specCase1.getEnsures().size());
        assertEquals(0, specCase1.getSignals().size());
        assertEquals(0, specCase1.getSignalsOnly().size());

        assertSame(specCase2.getBehavior(), Behavior.EXCEPTIONAL_BEHAVIOR);
        assertEquals(1, specCase2.getRequires().size());
        assertEquals(0, specCase2.getAssignable().size());
        assertEquals(0, specCase2.getEnsures().size());
        assertEquals(1, specCase2.getSignals().size());
        assertEquals(0, specCase2.getSignalsOnly().size());
    }

    @Test
    public void testAtInModelmethod() {
        parseMethodSpec(
                "/*@ model_behaviour\n" +
                        "  @   requires true;\n" +
                        "  @ model int f(int x) {\n" +
                        "  @   return x+1;\n" +
                        "  @ }\n" +
                        "  @*/");
    }

    @Test(expected = Exception.class)
    @Ignore
    public void disabled_testMLCommentEndInSLComment1() {
        parseMethodSpec("//@ requires @*/ true;");
        fail("Characters '@*/' should not be parsed");
    }

    @Test(expected = Exception.class)
    @Ignore
    public void disabled_testMLCommentEndInSLComment2() {
        parseMethodSpec("//@ requires */ true;");
    }

    @Test(expected = Exception.class)
    public void testFailure() {
        parseMethodSpec("/*@ normal_behaviour \n @ signals ohoh;  @*/");
        fail();
    }

    @Test(expected = Exception.class)
    public void testFailure2() {
        parseMethodSpec("/*@ behaviour\n"
                + "  @  requires (;((;;);();();(();;;(;)));\n"
                + "  @*/");
    }
}