/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;

import java.io.File;
import java.util.Arrays;

import org.key_project.logic.Name;
import org.key_project.rusty.ast.Converter;
import org.key_project.rusty.ast.ty.KeYRustyType;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.TacletIndex;
import org.key_project.rusty.proof.init.RustProfile;
import org.key_project.rusty.rule.NoPosTacletApp;
import org.key_project.rusty.rule.RuleApp;
import org.key_project.rusty.rule.TacletApp;
import org.key_project.rusty.util.TacletForTests;
import org.key_project.util.collection.ImmutableList;

import org.antlr.v4.runtime.CharStreams;
import org.antlr.v4.runtime.CommonTokenStream;
import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

public class BasicTest {
    public static final String STANDARD_RUST_RULES_KEY =
        "src/main/resources/org/key_project/rusty/proof/rules/standardRustRules.key";

    private static Semisequent parseTermForSemisequent(String t) {
        if ("".equals(t)) {
            return Semisequent.EMPTY_SEMISEQUENT;
        }
        SequentFormula cf0 = new SequentFormula(TacletForTests.parseTerm(t));
        return Semisequent.EMPTY_SEMISEQUENT.insert(0, cf0).semisequent();
    }

    private static Goal createGoal(Node n, TacletIndex tacletIndex) {
        // final BuiltInRuleAppIndex birIndex = new BuiltInRuleAppIndex(new BuiltInRuleIndex());
        return new Goal(n, tacletIndex, n.proof().getServices());
    }

    private static void applyRule(String name, PosInOccurrence pos, Proof proof) {
        NoPosTacletApp rule =
            TacletForTests.getRules().lookup(new Name(name));
        TacletIndex tacletIndex = new TacletIndex();
        tacletIndex.add(rule);
        var oldGoal = proof.openGoals().head();
        var goal = createGoal(oldGoal.getNode(), tacletIndex);
        proof.setOpenGoals(ImmutableList.of(goal));
        ImmutableList<TacletApp> rApplist =
            goal.ruleAppIndex().getTacletAppAt(pos, null);
        assertEquals(1, rApplist.size(), "Too many or zero rule applications.");
        RuleApp rApp = rApplist.head();
        assertTrue(rApp.complete(), "Rule App should be complete");
        goal.apply(rApp);
    }

    @Test
    void testStandardRuledParses() {
        TacletForTests.clear();
        TacletForTests.parse(new File(STANDARD_RUST_RULES_KEY));
    }

    @Test
    void testSimpleProgram() {
        TacletForTests.clear();
        TacletForTests.parse(new RustProfile());
        Semisequent antec = parseTermForSemisequent("");
        Semisequent succ = parseTermForSemisequent("\\<{ i = 2u32; i}\\>(i = 2)");
        Sequent s = Sequent.createSequent(antec, succ);
        var proof = new Proof(new Name("Simple"), s, TacletForTests.initConfig());
        applyRule("assignment",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel(), false),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println(proof.openGoals().head().sequent());
        // TODO: fix Term.equals: assertEquals(TacletForTests.parseTerm("{i:=2}\\<{i}\\>(i=2)"),
        // proof.openGoals().head().sequent().succedent().getFirst().formula());
        applyRule("emptyModality",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel().down(1), false),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println(proof.openGoals().head().sequent());
        applyRule("applyOnRigidFormula",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel(), false),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println(proof.openGoals().head().sequent());
        applyRule("applyOnPV",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel().down(0), false),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println(proof.openGoals().head().sequent());
        applyRule("applyOnRigidTerm",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel().down(1), false),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println(proof.openGoals().head().sequent());
        applyRule("applyOnRigidTerm",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel().down(1).down(0), false),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println(proof.openGoals().head().sequent());
        applyRule("simplifyUpdate1",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel().down(1).down(0).down(0), false),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println(proof.openGoals().head().sequent());
        applyRule("eqClose",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel(), false),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println(proof.openGoals().head().sequent());
        applyRule("closeTrue",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel(), false),
            proof);
        assertEquals(0, proof.openGoals().size());
        assertTrue(proof.closed());
        System.out.println("Proof successful!");
    }

    @Test
    public void testSwap() {
        // load
        TacletForTests.parse();
        assert TacletForTests.services().getNamespaces().programVariables()
                .lookup(new Name("i")) != null;

        var services = TacletForTests.services();
        var tb = services.getTermBuilder();

        var example = """
                {a = a + b;
                b = a - b;
                a = a - b;
                1u32
                }""";
        var lexer =
            new org.key_project.rusty.parsing.RustyWhileLexer(CharStreams.fromString(example));
        var ts = new CommonTokenStream(lexer);
        var parser = new org.key_project.rusty.parsing.RustyWhileParser(ts);
        var converter = new Converter(services);
        var block = converter.visitBlockExpr(parser.blockExpr());

        var intSort = services.getNamespaces().sorts().lookup("int");
        var intType = new KeYRustyType(intSort);

        var a = new ProgramVariable(new Name("a"), intSort, intType);
        var b = new ProgramVariable(new Name("b"), intSort, intType);
        var a_old = new ProgramVariable(new Name("a_old"), intSort, intType);
        var b_old = new ProgramVariable(new Name("b_old"), intSort, intType);

        services.getNamespaces().programVariables()
                .add(Arrays.stream(new ProgramVariable[] { a, a_old, b, b_old }).toList());

        var mod = tb.dia(new RustyBlock(block),
            tb.and(tb.equals(tb.var(a), tb.var(b_old)), tb.equals(tb.var(b), tb.var(a_old))));
        var t = tb.imp(
            tb.and(tb.equals(tb.var(a), tb.var(a_old)), tb.equals(tb.var(b), tb.var(b_old))),
            mod); // a = a_old && b = b_old -> <example> a = b_old && b = a_old
        System.out.println(t);


        Semisequent succ = new Semisequent(new SequentFormula(t));
        Sequent s = Sequent.createSuccSequent(succ);
        Proof p = new Proof("FirstProof", TacletForTests.initConfig());
        p.setRoot(new Node(p, s));

        p.getRoot().sequent().succedent().getFirst().formula();
        // continue manual proof like for example in TestApplyTaclet
    }

    @Test
    public void testInitialization() {

    }
}
