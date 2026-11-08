/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.parser;

import java.io.IOException;
import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.ContextStatementBlock;
import de.uka.ilkd.key.java.ast.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.ast.declaration.VariableSpecification;
import de.uka.ilkd.key.java.ast.expression.Assignment;
import de.uka.ilkd.key.java.ast.reference.ArrayReference;
import de.uka.ilkd.key.java.loader.JavaBuildingExceptions;
import de.uka.ilkd.key.java.loader.JavaBuildingIssue;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.nparser.KeyIO;
import de.uka.ilkd.key.pp.PrettyPrinter;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.metaconstruct.IsStatic;
import de.uka.ilkd.key.rule.metaconstruct.MethodCall;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.rule.tacletbuilder.*;
import de.uka.ilkd.key.util.parsing.BuildingException;

import org.key_project.logic.Name;
import org.key_project.logic.Namespace;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;
import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;

/**
 * class tests the parser for Taclets
 */


public class TestTacletParser {
    private static final String DECLS =
        ("""
                \\sorts { s; }
                \\functions {
                  s f(s);
                }
                \\schemaVariables {
                  \\formula b,b0,post;
                  \\program Statement #p1, #s ;\s
                  \\program Expression #e2, #e ;\s
                  \\program SimpleExpression #se ;\s
                  \\program MethodName #mn ;\s
                  \\program[list] SimpleExpression #selist ;\s
                  \\program Variable #slhs, #arr, #ar, #ar1 ;\s
                  \\program LoopInit #i ;\s
                  \\program Label #lab, #lb0, #lb1 ;\s
                  \\program Label #inner, #outer ;\s
                  \\program Type #typ ;\s
                  \\program Variable #v0, #v, #v1, #k, #boolv ;\s
                  \\program ExecutionContext #ex ;\s
                  \\program SimpleInstanceCreation #n ;\s
                  \\program ArrayInitializer #arrayinitializer ;\s
                  \\program[list] Catch #cf ;\s
                  \\term s x,x0 ;
                  \\skolemTerm s sk ;
                  \\variables s z,z0 ;
                }
                """);

    // set in parseDecls() from setUp(); null until then
    private @Nullable Namespace<SchemaVariable> schemaVariableNS;
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
        Namespace<SchemaVariable> ns = Objects
                .requireNonNull(schemaVariableNS, "the schema namespace must have been parsed");
        return Objects.requireNonNull(ns.lookup(new Name(name)), "schema variable " + name);
    }


    private void parseDecls(String s) throws IOException {
        KeyIO.Loader l = io.load(s);
        l.loadComplete();
        schemaVariableNS = l.getSchemaNamespace();
        io.setSchemaNamespace(
            Objects.requireNonNull(schemaVariableNS, "the schema namespace must be provided"));
    }

    public JTerm parseTerm(String s) {
        return io.parseExpression(s);
    }

    public JTerm parseFma(String s) {
        return parseTerm(s);
    }

    public SequentFormula cf(String s) {
        return new SequentFormula(parseFma(s));
    }

    // a null antecedent or succedent string denotes that the side of the sequent is empty
    public Sequent sequent(@Nullable String a, @Nullable String s) {
        var antec = ImmutableList.<SequentFormula>nil();
        var succ = ImmutableList.<SequentFormula>nil();
        if (a != null) {
            antec = ImmutableList.singleton(cf(a));
        }
        if (s != null) {
            succ = ImmutableList.singleton(cf(s));
        }
        return JavaDLSequentKit.createSequent(antec, succ);
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
        builder.addTacletGoalTemplate(
            new AntecSuccTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.nil(), sequent("b0", null)));

        builder.addTacletGoalTemplate(
            new AntecSuccTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.nil(), sequent(null, "b")));

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
        builder.addTacletGoalTemplate(
            new AntecSuccTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.nil(), sequent("b", "b0")));
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
            new TacletGoalTemplate(sequent("b", null), ImmutableList.nil()));

        builder.addTacletGoalTemplate(
            new TacletGoalTemplate(sequent(null, "b"), ImmutableList.nil()));
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
        builder.setAssumesSequent(sequent("b", null));
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
        builder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.nil(), parseFma("!b0->!b")));
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
        builder.addTacletGoalTemplate(
            new AntecSuccTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.nil(), sequent(null, "{\\subst z; sk}b")));
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
            new TacletGoalTemplate(sequent("{\\subst z; x}b", null), ImmutableList.nil()));
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
        builder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.nil(), parseFma("b & \\exists z; b0")));
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
        builder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.nil(), parseTerm("f(x)")));
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
        insertbuilder.addTacletGoalTemplate(
            new RewriteTacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.nil(), parseTerm("x0")));
        insertbuilder.setName(new Name("insert_eq"));
        Taclet inserteq = insertbuilder.getTaclet();

        AntecTacletBuilder builder = new AntecTacletBuilder();

        builder.setFind(parseFma("x=x0"));
        builder.addTacletGoalTemplate(
            new TacletGoalTemplate(JavaDLSequentKit.getInstance().getEmptySequent(),
                ImmutableList.<Taclet>singleton(inserteq)));
        builder.setName(new Name("make_insert_eq"));
        Taclet makeinserteq = builder.getAntecTaclet();
        String makeinserteqString = "make_insert_eq" + "{\\find (x = x0 ==>)"
            + "\\addrules ( insert_eq{\\find (x) \\replacewith (x0)} )}";
        assertEquals(makeinserteq, parseTaclet(makeinserteqString), "make-insert-eq");
    }

    @Test
    public void testSchemaJava0() {
        parseTaclet("while_right { \\find (\\<{.. while(#e2) {#p1} ...}\\>post)"
            + "\\replacewith (\\<{.. #unwindLoop (#inner, #outer, while(#e2) {#p1});  ...}\\>post) } ");

    }

    @Test
    public void testSchemaJava4() {
        FindTaclet taclet =
            (FindTaclet) parseTaclet("variable_declaration{ \\find (\\<{.. #typ #v0; ...}\\>post)"
                + " \\replacewith (\\<{.. #typ #v0; if (true); ...}\\>post)	}");
        JTerm find = taclet.find();
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
        JTerm find = taclet.find();
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
        JTerm find = taclet.find();
        JavaBlock jb = find.javaBlock();
        ContextStatementBlock ct = (ContextStatementBlock) jb.program();
    }

    @Test
    public void testSchemaJava10() {
        FindTaclet taclet = (FindTaclet) parseTaclet(
            "array_test {\\find(\\<{..#arr[#e][#e2]=#e2;...}\\>true) \\replacewith (true)}");
        JTerm find = taclet.find();
        JavaBlock jb = find.javaBlock();
        ContextStatementBlock ct = (ContextStatementBlock) jb.program();
        Assignment ca = (Assignment) ct.getChildAt(0);
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
        parseTaclet("""
                eval_order_array_access_right{
                    \\find(\\<{..#v=#ar[#e];...}\\>post)
                    \\varcond(\\newTypeOf(#ar1, #ar),\\newTypeOf(#v0, #e), \\newTypeOf(#k, #e))
                    \\replacewith(\\<{..for(#k=0;#k<#lengthReference(#ar);#k++){#ar1[#k]=#ar[#k];}
                                        #v0=#e; #v=#ar1[#v0];...}\\>post)
                    \\displayname "eval_order_array_access_right"
                }
                """);
    }

    @Test
    public void testSchemaJavaIsStatic() {
        FindTaclet taclet = (FindTaclet) parseTaclet(
            "isstatic_test {\\find(\\<{.. #v0 = #isstatic(#v); ...}\\>true) \\replacewith(true)}");
        JTerm find = taclet.find();
        JavaBlock jb = find.javaBlock();
        ContextStatementBlock ct = (ContextStatementBlock) jb.program();
        Assignment ca = (Assignment) ct.getChildAt(0);
        assertInstanceOf(IsStatic.class, ca.getChildAt(1));
    }

    @Test
    public void testMethodCallRejectsWrongSortExecutionContext() {
        // 3-arg form (ProgramSV ec, SchemaVariable result, ProgramElement body): slot 0 is the
        // execution context. Passing a VARIABLE-sort #v0 there must be rejected at parse time
        // with a positioned reportError instead of being silently accepted.
        BuildingException e = assertThrows(BuildingException.class, () -> parseTaclet(
            "badMethodCall {\\find(\\<{.. #methodCall(#v0, #v, #s); ...}\\>true)"
                + " \\replacewith(true)}"));
        assertTrue(hasCause(e, JavaBuildingExceptions.class),
            "wrong execution-context sort must surface as reportError, but was: " + e.getMessage());
    }

    @Test
    public void testMethodCallRejectsUnsupportedProgramSort() {
        // Single-ProgramSV form: #p1 has STATEMENT sort, which is neither EXECUTIONCONTEXT nor
        // VARIABLE, so it must not be silently nulled but rejected at parse time.
        BuildingException e = assertThrows(BuildingException.class, () -> parseTaclet(
            "badMethodCall {\\find(\\<{.. #methodCall(#p1, #s); ...}\\>true)"
                + " \\replacewith(true)}"));
        assertTrue(hasCause(e, JavaBuildingExceptions.class),
            "unsupported program sort must surface as reportError, but was: " + e.getMessage());
    }

    @Test
    public void testIsStaticZeroArgsRejected() {
        // Expression-position transformers take exactly one argument. #isstatic() with zero
        // arguments must yield a parse error rather than an IndexOutOfBoundsException.
        BuildingException e = assertThrows(BuildingException.class, () -> parseTaclet(
            "badIsStatic {\\find(\\<{.. #v0 = #isstatic(); ...}\\>true) \\replacewith(true)}"));
        assertFalse(hasCause(e, IndexOutOfBoundsException.class),
            "zero-arg #isstatic must not crash with IndexOutOfBoundsException");
        assertTrue(hasCause(e, JavaBuildingExceptions.class),
            "zero-arg #isstatic must surface as reportError, but was: " + e.getMessage());
    }

    @Test
    public void testLengthReferenceTwoArgsRejected() {
        // Expression-position transformers take exactly one argument. #lengthReference(a, b)
        // with two arguments must be rejected rather than silently dropping the second.
        BuildingException e = assertThrows(BuildingException.class, () -> parseTaclet(
            "badLength {\\find(\\<{.. #v0 = #lengthReference(#ar, #ar1); ...}\\>true)"
                + " \\replacewith(true)}"));
        assertTrue(hasCause(e, JavaBuildingExceptions.class),
            "two-arg #lengthReference must surface as reportError, but was: " + e.getMessage());
    }

    @Test
    public void testMethodCallResultVarRoundtrips() {
        // The pretty printer must emit every #methodCall schema-variable argument so that a rule
        // can
        // be printed and re-parsed (Agent-KeY needs roundtrippable rules). The result variable #v0
        // must survive a print + re-parse cycle instead of being dropped.
        FindTaclet original = (FindTaclet) parseTaclet("methodCallRt {\\find(\\<{.. "
            + "#methodCall(#v0, #se.#mn(#selist)); ...}\\>true) \\replacewith(true)}");

        // the parsed \find contains the MethodCall transformer as its single statement
        ContextStatementBlock block =
            (ContextStatementBlock) original.find().javaBlock().program();
        MethodCall mc = (MethodCall) block.getChildAt(0);

        // serialise exactly the meta-construct, as the pretty printer does during rule output
        PrettyPrinter pp = PrettyPrinter.purePrinter();
        pp.printFragment(mc);
        String printed = pp.result();

        assertTrue(printed.contains("#methodCall(#v0,"),
            "printed #methodCall must keep its result variable, but was:\n" + printed);

        // the printed fragment must re-parse as a rule holding the same meta-construct
        Taclet reparsed =
            parseTaclet("rt2 {\\find(\\<{.. " + printed + "; ...}\\>true) \\replacewith(true)}");
        assertNotNull(reparsed);
    }

    @Test
    public void testMetaConstructErrorCarriesPosition() {
        // A broken meta-construct must surface a positioned parsing error (a real line/column,
        // not the -1 that PositionInfo.UNDEFINED corresponds to).
        BuildingException e = assertThrows(BuildingException.class, () -> parseTaclet(
            "badIsStatic {\\find(\\<{.. #v0 = #isstatic(); ...}\\>true) \\replacewith(true)}"));
        JavaBuildingExceptions jbe =
            (JavaBuildingExceptions) causeOf(e, JavaBuildingExceptions.class);
        assertNotNull(jbe);
        JavaBuildingIssue issue = jbe.getIssues().get(0);
        assertNotEquals(-1, issue.getLine(), "error must carry a real line number");
        assertNotEquals(-1, issue.getColumn(), "error must carry a real column number");
    }

    @Test
    public void testMethodCallRejectsWrongSortResultVariable() {
        // 3-arg form: slot 1 is the result variable and must be a program variable. A
        // Statement-sort schema variable there must be rejected at parse time.
        BuildingException e = assertThrows(BuildingException.class, () -> parseTaclet(
            "badMethodCallResult {\\find(\\<{.. #methodCall(#ex, #p1, #s); ...}\\>true)"
                + " \\replacewith(true)}"));
        assertTrue(hasCause(e, JavaBuildingExceptions.class),
            "wrong result-variable sort must surface as reportError, but was: " + e.getMessage());
    }

    @Test
    public void testMetaConstructArgumentsRoundtrip() {
        // The pretty printer must emit every schema-variable argument of a meta construct, not
        // only #methodCall's, so that rules can be printed and re-parsed (Agent-KeY needs
        // roundtrippable rules).
        assertMetaConstructRoundtrips("unwindLoopRt",
            "#unwindLoop(#inner, #outer, while (#e) #s)", "#unwindLoop(#inner,");
        assertMetaConstructRoundtrips("constructorCallRt",
            "#constructorCall(#v0, #n)", "#constructorCall(#v0,");
        assertMetaConstructRoundtrips("initArrayCreationRt",
            "#initArrayCreation(#v0, #arrayinitializer)", "#initArrayCreation(#v0,");
    }

    private void assertMetaConstructRoundtrips(String name, String metaConstruct,
            String expectedPrefix) {
        FindTaclet original = (FindTaclet) parseTaclet(name + " {\\find(\\<{.. "
            + metaConstruct + "; ...}\\>true) \\replacewith(true)}");
        ContextStatementBlock block =
            (ContextStatementBlock) original.find().javaBlock().program();
        ProgramTransformer transformer = (ProgramTransformer) block.getChildAt(0);

        PrettyPrinter pp = PrettyPrinter.purePrinter();
        pp.printFragment(transformer);
        String printed = pp.result();

        assertTrue(printed.contains(expectedPrefix),
            "printed meta construct must keep its schema-variable arguments, but was:\n"
                + printed);

        Taclet reparsed = parseTaclet(
            name + "Reparsed {\\find(\\<{.. " + printed + "; ...}\\>true) \\replacewith(true)}");
        assertNotNull(reparsed);
    }

    private static boolean hasCause(Throwable t, Class<? extends Throwable> type) {
        return causeOf(t, type) != null;
    }

    private static Throwable causeOf(Throwable t, Class<? extends Throwable> type) {
        for (Throwable c = t; c != null; c = c.getCause()) {
            if (type.isInstance(c)) {
                return c;
            }
        }
        return null;
    }

    @Test
    public void testFreeReplacewithVariables() {
        // broken taclet with free variable SV in replacewith
        // buggy { find(==>b) replacewith(==>b,z=z) }

        String brokenTacletString = "buggy { \\find(==>b)" + "\\replacewith(==>b,z=z) }";
        Assertions.assertThrows(TacletBuilder.TacletBuilderException.class, () -> {
            parseTaclet(brokenTacletString);
        });
    }


    // Following tests should work, if parser didn't exit system but propagated
    // exceptions until here.
    @Test
    public void testSchemaJava1() {
        boolean thrown = false;
        try {
            parseTaclet("xyz { find (<{.. int j=0; for(#i;j<9;j++)" + "; ...}>post)"
                + "replacewith (<{.. #unwindLoop (while(#e2) {#p1});" + "  ...}>post) } ");
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
                + "replacewith (<{.. #unwindLoop (while(#e2) {#p1});  ...}>post) } ");
        } catch (RuntimeException e) {
            thrown = true;
        }
        assertTrue(thrown, "label SV not valid here");
    }

    // more SchemaJava tests are in ../rule/TestMatchTaclet
}
