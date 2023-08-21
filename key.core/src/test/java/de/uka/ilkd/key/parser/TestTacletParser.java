/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.parser;

import java.io.IOException;
import java.util.List;

import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.tacletbuilder.*;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * class tests the parser for Taclets
 */


public class TestTacletParser {
    private static final String DECLS =
        ("\\sorts { s; }\n" + "\\functions {\n" + "  s f(s);\n" + "}\n" + "\\schemaVariables {\n"
            + "  \\formula b,b0,post;\n" + "  \\program Statement #p1, #s ; \n"
            + "  \\program Expression #e2, #e ; \n" + "  \\program SimpleExpression #se ; \n"
            + "  \\program Variable #slhs, #arr, #ar, #ar1 ; \n" + "  \\program LoopInit #i ; \n"
            + "  \\program Label #lab, #lb0, #lb1 ; \n" + "  \\program Label #inner, #outer ; \n"
            + "  \\program Type #typ ; \n" + "  \\program Variable #v0, #v, #v1, #k, #boolv ; \n"
            + "  \\program[list] Catch #cf ; \n" + "  \\term s x,x0 ;\n" + "  \\skolemTerm s sk ;\n"
            + "  \\variables s z,z0 ;\n" + "}\n");

    private Namespace<SchemaVariable> schemaVariableNS;
    private KeyIO io;

    @BeforeEach
    public void setUp() throws IOException {
        NamespaceSet nss = new NamespaceSet();
        Services services = TacletForTests.services();
        io = new KeyIO(services, nss);
        parseDecls(DECLS);
    }

    //
    // Utility methods for setUp:
    //

    private SchemaVariable lookup_schemavar(String name) {
        return schemaVariableNS.lookup(new Name(name));
    }


    private void parseDecls(String s) throws IOException {
        KeyIO.Loader l = io.load(s);
        l.loadComplete();
        schemaVariableNS = l.getSchemaNamespace();
        io.setSchemaNamespace(schemaVariableNS);
    }

    public Term parseTerm(String s) {
        return io.parseExpression(s);
    }

    public Term parseFma(String s) {
        return parseTerm(s);
    }

    public SequentFormula cf(String s) {
        return new SequentFormula(parseFma(s));
    }

    public Semisequent sseq(String s) {
        return Semisequent.EMPTY_SEMISEQUENT.insertFirst(cf(s)).semisequent();
    }

    public Sequent sequent(String a, String s) {
        Semisequent ass = Semisequent.EMPTY_SEMISEQUENT;
        Semisequent sss = Semisequent.EMPTY_SEMISEQUENT;
        if (a != null) {
            ass = sseq(a);
        }
        if (s != null) {
            sss = sseq(s);
        }
        return Sequent.createSequent(ass, sss);
    }

    Taclet parseTaclet(String s) {
        s = "\n\\rules { " + s + "; }";
        try {
            KeyIO.Loader l = io.load(s);
            List<Taclet> taclets = l.loadComplete();
            return taclets.get(0);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }


    @Test
    public void testImpLeft() {
        // imp-left rule
        // find(b->b0 =>) replacewith(b0 =>) replacewith(=> b)
        AntecTacletBuilder builder = new AntecTacletBuilder();
        builder.setFind(parseFma("b->b0"));
        builder.setName(new Name("imp_left"));
        builder.addTacletGoalTemplate(new AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
            ImmutableSLList.nil(), sequent("b0", null)));

        builder.addTacletGoalTemplate(new AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
            ImmutableSLList.nil(), sequent(null, "b")));

        Taclet impleft = builder.getAntecTaclet();
        String impleftString =
            "imp_left{\\find(b->b0 ==>) \\replacewith(b0 ==>); \\replacewith(==> b)}";
        assertEquals(impleft, parseTaclet(impleftString), "imp-left");
    }

    @Test
    public void testImpRight() {
        // imp-right rule
        // find(=> b->b0) replacewith(b => b0)
        SuccTacletBuilder builder = new SuccTacletBuilder();
        builder.setFind(parseFma("b->b0"));
        builder.addTacletGoalTemplate(new AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
            ImmutableSLList.nil(), sequent("b", "b0")));
        builder.setName(new Name("imp_right"));
        Taclet impright = builder.getSuccTaclet();
        String imprightString = "imp_right{\\find(==> b->b0) \\replacewith(b ==> b0)}";

        assertEquals(impright, parseTaclet(imprightString), "imp-right");
    }

    @Test
    public void testCut() {
        // cut rule
        // add(b=>) add(=>b)
        NoFindTacletBuilder builder = new NoFindTacletBuilder();
        builder.addTacletGoalTemplate(
            new TacletGoalTemplate(sequent("b", null), ImmutableSLList.nil()));

        builder.addTacletGoalTemplate(
            new TacletGoalTemplate(sequent(null, "b"), ImmutableSLList.nil()));
        builder.setName(new Name("cut"));

        Taclet cut = builder.getNoFindTaclet();
        String cutString = "cut{\\add(b==>); \\add(==>b)}";
        assertEquals(cut, parseTaclet(cutString));
    }

    @Test
    public void testClose() {
        // close rule
        // if (b=>) find(=>b)
        SuccTacletBuilder builder = new SuccTacletBuilder();
        builder.setFind(parseFma("b"));
        builder.setIfSequent(sequent("b", null));
        builder.setName(new Name("close_goal"));
        Taclet close = builder.getSuccTaclet();
        String closeString = "close_goal{\\assumes (b==>) \\find(==>b) \\closegoal}";
        assertEquals(close, parseTaclet(closeString), "close");
    }

    @Test
    public void testContraposition() {
        // contraposition rule
        // find(b->b0) replacewith(-b0 -> -b)

        RewriteTacletBuilder<RewriteTaclet> builder = new RewriteTacletBuilder<>();
        builder.setFind(parseFma("b->b0"));
        builder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
            ImmutableSLList.nil(), parseFma("!b0->!b")));
        builder.setName(new Name("contraposition"));
        Taclet contraposition = builder.getRewriteTaclet();
        String contrapositionString = "contraposition{\\find(b->b0) \\replacewith(!b0 -> !b)}";

        assertEquals(contraposition, parseTaclet(contrapositionString), "contraposition");
    }

    @Test
    public void testAllRight() {
        // all-right rule
        // find (==> all z.b) varcond ( sk new depending on b ) replacewith (==> {z sk}b)
        SuccTacletBuilder builder = new SuccTacletBuilder();

        builder.setFind(parseFma("\\forall z; b"));
        builder.addTacletGoalTemplate(new AntecSuccTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
            ImmutableSLList.nil(), sequent(null, "{\\subst z; sk}b")));
        builder.addVarsNewDependingOn(lookup_schemavar("sk"), lookup_schemavar("b"));
        builder.setName(new Name("all_right"));
        Taclet allright = builder.getSuccTaclet();
        String allrightString =
            "all_right{\\find (==> \\forall z; b) \\varcond ( \\newDependingOn(sk, b) ) \\replacewith (==> {\\subst z; sk}b)}";
        assertEquals(allright, parseTaclet(allrightString), "all-right");
    }

    @Test
    public void testAllLeft() {
        // all-left rule
        // find(all z . b==>) add({z x}b==>)
        AntecTacletBuilder builder = new AntecTacletBuilder();

        builder.setFind(parseFma("\\forall z; b"));


        builder.addTacletGoalTemplate(
            new TacletGoalTemplate(sequent("{\\subst z; x}b", null), ImmutableSLList.nil()));
        builder.setName(new Name("all_left"));
        Taclet allleft = builder.getAntecTaclet();
        String allleftString = "all_left{\\find(\\forall z; b==>) \\add({\\subst z; x}b==>)}";
        assertEquals(allleft, parseTaclet(allleftString), "all-left");
    }

    @Test
    public void testExConjSplit() {
        // exists-conj-split rule
        // find(ex z . ( b & b0 )) varcond(z not free in b)
        // replacewith( b & ex z.b0 )

        RewriteTacletBuilder<RewriteTaclet> builder = new RewriteTacletBuilder<>();
        builder.setFind(parseFma("\\exists z; (b & b0)"));
        builder.addVarsNotFreeIn(lookup_schemavar("z"), lookup_schemavar("b"));
        builder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
            ImmutableSLList.nil(), parseFma("b & \\exists z; b0")));
        builder.setName(new Name("exists_conj_split"));
        Taclet exconjsplit = builder.getRewriteTaclet();
        String exconjsplitString =
            "exists_conj_split{" + "\\find(\\exists z; ( b & b0 )) \\varcond(\\notFreeIn(z, b)) \n"
                + "\\replacewith( b & \\exists z; b0 )}";
        assertEquals(exconjsplit, parseTaclet(exconjsplitString), "ex-conj-split");
    }

    @Test
    public void testFIdempotent() {
        // f-idempotent-rule
        // find(f(f(x))) replacewith( f(x) )

        RewriteTacletBuilder<RewriteTaclet> builder = new RewriteTacletBuilder<>();

        builder.setFind(parseTerm("f(f(x))"));
        builder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
            ImmutableSLList.nil(), parseTerm("f(x)")));
        builder.setName(new Name("f_idempotent"));
        Taclet fidempotent = builder.getRewriteTaclet();
        String fidempotentString = "f_idempotent{\\find(f(f(x))) \\replacewith(f(x))}";
        assertEquals(fidempotent, parseTaclet(fidempotentString), "f-idempotent");
    }

    @Test
    public void testMakeInsertEq() {
        // make-insert-eq rule
        // find (x = x0 =>) addrules ( find (x) replacewith (x0) )
        RewriteTacletBuilder<RewriteTaclet> insertbuilder = new RewriteTacletBuilder<>();
        insertbuilder.setFind(parseTerm("x"));
        insertbuilder.addTacletGoalTemplate(new RewriteTacletGoalTemplate(Sequent.EMPTY_SEQUENT,
            ImmutableSLList.nil(), parseTerm("x0")));
        insertbuilder.setName(new Name("insert_eq"));
        Taclet inserteq = insertbuilder.getTaclet();

        AntecTacletBuilder builder = new AntecTacletBuilder();

        builder.setFind(parseFma("x=x0"));
        builder.addTacletGoalTemplate(new TacletGoalTemplate(Sequent.EMPTY_SEQUENT,
            ImmutableSLList.<Taclet>nil().prepend(inserteq)));
        builder.setName(new Name("make_insert_eq"));
        Taclet makeinserteq = builder.getAntecTaclet();
        String makeinserteqString = "make_insert_eq" + "{\\find (x = x0 ==>)"
            + "\\addrules ( insert_eq{\\find (x) \\replacewith (x0)} )}";
        assertEquals(makeinserteq, parseTaclet(makeinserteqString), "make-insert-eq");
    }

    @Test
    public void testSchemaJava0() {
        parseTaclet("while_right { \\find (\\<{.. while(#e2) {#p1} ...}\\>post)"
            + "\\replacewith (\\<{.. #unwind-loop (#inner, #outer, while(#e2) {#p1});  ...}\\>post) } ");

    }

    @Test
    public void testSchemaJava4() {
        FindTaclet taclet =
            (FindTaclet) parseTaclet("variable_declaration{ \\find (\\<{.. #typ #v0; ...}\\>post)"
                + " \\replacewith (\\<{.. #typ #v0; if (true); ...}\\>post)	}");
        Term find = taclet.find();
        JavaBlock jb = find.javaBlock();

        ContextStatementBlock ct = (ContextStatementBlock) jb.program();
        LocalVariableDeclaration lvd = (LocalVariableDeclaration) ct.getChildAt(0);
        lvd.getChildAt(1);

    }

    @Test
    public void testVarcondNew() {
        parseTaclet("xy{ \\find (true) \\varcond(\\new(#boolv,long)) \\replacewith(true)}");
        parseTaclet("xy{ \\find (true) \\varcond (\\newTypeOf(#v0, #e2)) \\replacewith(true)}");
    }

    @Test
    public void testSchemaJava6() {
        FindTaclet taclet =
            (FindTaclet) parseTaclet("xy{ \\find (\\<{.. boolean #boolv; ...}\\>post)"
                + " \\replacewith (\\<{.. if (true); ...}\\>post)	}");
        Term find = taclet.find();
        JavaBlock jb = find.javaBlock();

        ContextStatementBlock ct = (ContextStatementBlock) jb.program();
        LocalVariableDeclaration lvd = (LocalVariableDeclaration) ct.getChildAt(0);
        VariableSpecification vs = (VariableSpecification) lvd.getChildAt(1);
    }


    @Test
    public void testSchemaJava8() {
        FindTaclet taclet =
            (FindTaclet) parseTaclet("break_test {\\find(\\<{.. #lb0:{ break #lb1; } ...}\\>post)"
                + " \\replacewith (\\<{..  ...}\\>post)}");
        Term find = taclet.find();
        JavaBlock jb = find.javaBlock();
        ContextStatementBlock ct = (ContextStatementBlock) jb.program();
    }

    @Test
    public void testSchemaJava10() {
        FindTaclet taclet = (FindTaclet) parseTaclet(
            "array_test {\\find(\\<{..#arr[#e][#e2]=#e2;...}\\>true) \\replacewith (true)}");
        Term find = taclet.find();
        JavaBlock jb = find.javaBlock();
        ContextStatementBlock ct = (ContextStatementBlock) jb.program();
        CopyAssignment ca = (CopyAssignment) ct.getChildAt(0);
        ArrayReference ar = (ArrayReference) ca.getChildAt(0);
        for (int i = 0; i < 2; i++) {
            assertNotNull(ar.getChildAt(i));
        }
        ar = (ArrayReference) ar.getChildAt(0);
        for (int i = 0; i < 2; i++) {
            assertNotNull(ar.getChildAt(i));
        }
    }

    @Test
    public void testSchemaJava11() {
        parseTaclet("eval_order_array_access_right{" + " \\find(\\<{..#v=#ar[#e];...}\\>post)"
            + "\\varcond(\\newTypeOf(#ar1, #ar)," + "\\newTypeOf(#v0, #e), \\newTypeOf(#k, #e))"
            + "\\replacewith(\\<{..for(#k=0;#k<#length-reference(#ar);#k++){" + "#ar1[#k]=#ar[#k];}"
            + "#v0=#e; #v=#ar1[#v0];...}\\>post)"
            + "\\displayname \"eval_order_array_access_right\"}");
    }


    @Test
    public void testFreeReplacewithVariables() {
        // broken taclet with free variable SV in replacewith
        // buggy { find(==>b) replacewith(==>b,z=z) }

        String brokenTacletString = "buggy { \\find(==>b)" + "\\replacewith(==>b,z=z) }";
        try {
            parseTaclet(brokenTacletString);
            // p.setSchemaVariablesNamespace(schemaVariableNS);
            fail("Expected the taclet builder to throw an exception "
                + "because of free variables in replacewith");
        } catch (Exception e) {
            assertTrue(e instanceof BuildingException,
                "Expected BuildingException, but got " + e.getClass());
        }
    }


    // Following tests should work, if parser didn't exit system but propagated
    // exceptions until here.
    @Test
    public void testSchemaJava1() {
        boolean thrown = false;
        try {
            parseTaclet("xyz { find (<{.. int j=0; for(#i;j<9;j++)" + "; ...}>post)"
                + "replacewith (<{.. #unwind-loop (while(#e2) {#p1});" + "  ...}>post) } ");
        } catch (RuntimeException e) {
            thrown = true;
        }
        assertTrue(thrown, "forinit only valid in initializer of for");
    }


    @Test
    public void testSchemaJava2() {
        boolean thrown = false;
        try {
            parseTaclet("xyz { find (<{.. int j=0; for(#lab;j<42;j++) ; ...}>post)"
                + "replacewith (<{.. #unwind-loop (while(#e2) {#p1});  ...}>post) } ");
        } catch (RuntimeException e) {
            thrown = true;
        }
        assertTrue(thrown, "label SV not valid here");
    }

    // more SchemaJava tests are in ../rule/TestMatchTaclet
}
