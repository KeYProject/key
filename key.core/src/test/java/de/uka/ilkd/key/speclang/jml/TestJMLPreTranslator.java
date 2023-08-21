/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang.jml;

import de.uka.ilkd.key.speclang.jml.pretranslation.Behavior;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLSpecCase;
import de.uka.ilkd.key.speclang.njml.*;

import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.Token;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Disabled;
import org.junit.jupiter.api.Test;

import static de.uka.ilkd.key.speclang.njml.JmlLexer.*;
import static org.junit.jupiter.api.Assertions.*;


public class TestJMLPreTranslator {
    private ImmutableList<TextualJMLConstruct> parseMethodSpec(String ms) {
        return new PreParser().parseClassLevel(ms);
    }

    // region lexing
    @Test
    public void testMarkerDecision() {
        JmlMarkerDecision m = new JmlMarkerDecision(null);
        assertFalse(m.isActiveJmlSpec("+OPENJML"));
        assertFalse(m.isActiveJmlSpec("-key+key"));
        assertTrue(m.isActiveJmlSpec("-other"));
        assertTrue(m.isActiveJmlSpec("+key"));
        assertTrue(m.isActiveJmlSpec("+KEY"));
        assertFalse(m.isActiveJmlSpec("-"));
        assertTrue(m.isActiveJmlSpec("key"));
        assertFalse(m.isActiveJmlSpec("+"));

    }

    @Test
    public void testEnabledKeysLexer() {
        String contract = "/*-key@ invariant x == 54; */";
        lex(contract, COMMENT);
    }

    @Test
    public void testLexer1() {
        String in = "/*@ normal_behavior\n" + "     requires true;\n" + "  */";
        lex(in, JML_ML_START, WS, NORMAL_BEHAVIOR, WS, REQUIRES);
    }

    @Test
    public void testLexer2() {
        lex("ensures //-key@ this should be ignored\n" + "true;", ENSURES, WS, COMMENT, WS, TRUE,
            SEMI_TOPLEVEL, EOF);
    }

    @Test
    public void testLexer3() {
        lex("ensures      /*-key@ this should be ignored */ true;", ENSURES, WS, COMMENT, WS, TRUE,
            SEMI_TOPLEVEL, EOF);
    }

    @Test
    public void testLexer4() {
        lex("/*-openjml@ ensures true; */", JML_ML_START, WS, ENSURES, WS, TRUE, SEMI_TOPLEVEL, WS,
            JML_ML_END, EOF);
    }

    @Test
    public void testLexer5() {
        lex("/*@ pure */ /*@ ensures true;", JML_ML_START, WS, PURE, WS, JML_ML_END, WS,
            JML_ML_START, WS, ENSURES, WS, TRUE, SEMI_TOPLEVEL, EOF);
    }

    @Test
    public void testLexer6() {
        lex("//@ normal_behaviour\n" + "//@  ensures false\n" + "//@          || true;\n"
            + "//@  assignable \\nothing;\n" + "//@ also exceptional_behaviour\n"
            + "//@  requires o == null;\n" + "//@  signals Exception;\n", JML_SL_START, WS,
            NORMAL_BEHAVIOR, WS, JML_SL_START, WS, ENSURES, WS);
    }

    @Test
    public void testLexer7() {
        lex("//+ESC@ special comment for ESC", SL_COMMENT);
    }

    @Test
    public void testLexer8() {
        lex("//+ESC+key@ behaviour", JML_SL_START, WS, BEHAVIOR);
    }

    @Test
    public void testLexer9() {
        lex("//+ESC+key-key@ behaviour", SL_COMMENT);
    }

    @Test
    public void testLexer10() {
        lex("//-@ behaviour", SL_COMMENT);
        lex("//+key+@ behaviour", SL_COMMENT);
        // unclear which is wanted for "//key@ behaviour"
        // currently "key" is ignored
    }

    private void lex(String in, int... expected) {
        JmlLexer lexer = JmlFacade.createLexer(in);
        Token t;
        int idx = 0;
        do {
            t = lexer.nextToken();
            System.out.printf("%s\n", t);
            if (idx < expected.length) {
                Assertions.assertEquals(expected[idx], t.getType(),
                    String.format("Token wanted '%s', but got '%s'. ",
                        lexer.getVocabulary().getDisplayName(expected[idx]),
                        lexer.getVocabulary().getDisplayName(t.getType())));
                idx++;
            }
        } while (t.getType() != -1);
    }
    // endregion

    @Test
    public void testSimpleSpec() {
        ImmutableList<TextualJMLConstruct> constructs =
            parseMethodSpec("/*@ normal_behavior\n" + "     requires true;\n" + "  */");

        Assertions.assertNotNull(constructs);
        Assertions.assertEquals(1, constructs.size());
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase = (TextualJMLSpecCase) constructs.head();

        Assertions.assertSame(Behavior.NORMAL_BEHAVIOR, specCase.getBehavior());
        Assertions.assertEquals(1, specCase.getRequires().size());
        Assertions.assertEquals(0, specCase.getAssignable().size());
        Assertions.assertEquals(0, specCase.getEnsures().size());
        Assertions.assertEquals(0, specCase.getSignals().size());
        Assertions.assertEquals(0, specCase.getSignalsOnly().size());
        Assertions.assertEquals("requirestrue;",
            specCase.getRequires().head().first.getText().trim());
    }


    @Test
    public void testComplexSpec() {
        ImmutableList<TextualJMLConstruct> constructs =
            parseMethodSpec("/*@ behaviour\n" + "  @  requires true;\n"
                + "  @  requires a!=null && (\\forall int i; 0 <= i && i <= 2; \\dl_f(i) );\n"
                + "  @  ensures false;\n" + "  @  signals (Exception) e;\n"
                + "  @  signals_only onlythis;\n" + "  @  assignable \\nothing;\n" + "  @*/");

        Assertions.assertNotNull(constructs);
        Assertions.assertEquals(1, constructs.size());
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase = (TextualJMLSpecCase) constructs.head();

        Assertions.assertSame(Behavior.BEHAVIOR, specCase.getBehavior());
        Assertions.assertEquals(2, specCase.getRequires().size());
        Assertions.assertEquals(1, specCase.getAssignable().size());
        Assertions.assertEquals(1, specCase.getEnsures().size());
        Assertions.assertEquals(1, specCase.getSignals().size());
        Assertions.assertEquals(1, specCase.getSignalsOnly().size());

        System.out.println(specCase);

        Assertions.assertEquals("ensuresfalse;",
            specCase.getEnsures().head().first.getText().trim());
        Assertions.assertEquals("assignable\\nothing;",
            specCase.getAssignable().head().first.getText().trim());
        Assertions.assertEquals("signals(Exception)e;",
            specCase.getSignals().head().first.getText().trim());
        Assertions.assertEquals("signals_onlyonlythis;",
            specCase.getSignalsOnly().head().first.getText().trim());
        Assertions.assertEquals("requirestrue;",
            specCase.getRequires().head().first.getText().trim());
    }


    @Test
    public void testMultipleSpecs() {
        ImmutableList<TextualJMLConstruct> constructs = parseMethodSpec(
            "//@ normal_behaviour\n" + "//@  ensures false\n" + "//@          || true;\n"
                + "//@  assignable \\nothing;\n" + "//@ also exceptional_behaviour\n"
                + "//@  requires o == null;\n" + "//@  signals (Exception) e;\n");

        Assertions.assertNotNull(constructs);
        Assertions.assertEquals(2, constructs.size());
        assertTrue(constructs.head() instanceof TextualJMLSpecCase);
        assertTrue(constructs.tail().head() instanceof TextualJMLSpecCase);
        TextualJMLSpecCase specCase1 = (TextualJMLSpecCase) constructs.head();
        TextualJMLSpecCase specCase2 = (TextualJMLSpecCase) constructs.tail().head();

        Assertions.assertSame(Behavior.NORMAL_BEHAVIOR, specCase1.getBehavior());
        Assertions.assertEquals(0, specCase1.getRequires().size());
        Assertions.assertEquals(1, specCase1.getAssignable().size());
        Assertions.assertEquals(1, specCase1.getEnsures().size());
        Assertions.assertEquals(0, specCase1.getSignals().size());
        Assertions.assertEquals(0, specCase1.getSignalsOnly().size());

        Assertions.assertSame(Behavior.EXCEPTIONAL_BEHAVIOR, specCase2.getBehavior());
        Assertions.assertEquals(1, specCase2.getRequires().size());
        Assertions.assertEquals(0, specCase2.getAssignable().size());
        Assertions.assertEquals(0, specCase2.getEnsures().size());
        Assertions.assertEquals(1, specCase2.getSignals().size());
        Assertions.assertEquals(0, specCase2.getSignalsOnly().size());
    }

    @Test
    public void testAtInModelmethod() {
        parseMethodSpec("/*@ model_behaviour\n" + "  @   requires true;\n"
            + "  @ model int f(int x) {\n" + "  @   return x+1;\n" + "  @ }\n" + "  @*/");
    }

    @Test
    @Disabled
    public void disabled_testMLCommentEndInSLComment1() {
        assertThrows(Exception.class, () -> parseMethodSpec("//@ requires @*/ true;"),
            "Characters '@*/' should not be parsed");
    }

    @Test
    @Disabled
    public void disabled_testMLCommentEndInSLComment2() {
        parseMethodSpec("//@ requires */ true;");
    }

    @Test
    public void testFailure() {
        assertThrows(Exception.class,
            () -> parseMethodSpec("/*@ normal_behaviour \n @ signals ohoh;  @*/"));
    }

    @Test
    public void testFailure2() {
        assertThrows(Exception.class, () -> parseMethodSpec(
            "/*@ behaviour\n" + "  @  requires (;((;;);();();(();;;(;)));\n" + "  @*/"));
    }
}
