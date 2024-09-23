/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty;

import java.io.File;
import java.io.IOException;

import org.key_project.logic.Name;
import org.key_project.rusty.ast.abstraction.KeYRustyType;
import org.key_project.rusty.logic.*;
import org.key_project.rusty.logic.op.Modality;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.proof.Goal;
import org.key_project.rusty.proof.Node;
import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.TacletIndex;
import org.key_project.rusty.proof.init.RustProfile;
import org.key_project.rusty.proof.io.ProofSaver;
import org.key_project.rusty.rule.NoPosTacletApp;
import org.key_project.rusty.rule.RuleApp;
import org.key_project.rusty.rule.TacletApp;
import org.key_project.rusty.util.TacletForTests;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.*;
import static org.key_project.rusty.logic.equality.RenamingProgramElementProperty.RENAMING_PROGRAM_ELEMENT_PROPERTY;

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
        applyRule(name, pos, proof, 0);
    }

    private static void applyRule(String name, PosInOccurrence pos, Proof proof, int index) {
        NoPosTacletApp rule =
            TacletForTests.getRules().lookup(new Name(name));
        TacletIndex tacletIndex = new TacletIndex();
        tacletIndex.add(rule);
        var oldGoals = proof.openGoals();
        var goal = createGoal(oldGoals.get(index).getNode(), tacletIndex);
        ImmutableList<Goal> newGoals = ImmutableSLList.nil();
        for (int i = 0; i < oldGoals.size(); ++i) {
            if (i == index)
                newGoals = newGoals.append(goal);
            else
                newGoals = newGoals.append(oldGoals.get(i));
        }
        proof.setOpenGoals(newGoals);
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
        try {
            ProofSaver.saveToFile(new File("simple.proof"), proof);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Test
    void testIf() {
        TacletForTests.clear();
        TacletForTests.parse(new RustProfile());
        Semisequent antec = parseTermForSemisequent("");
        Semisequent succ =
            parseTermForSemisequent("\\<{ b = false; if b {i = 3u32} else {i = 2u32} i}\\>(i = 2)");
        Sequent s = Sequent.createSequent(antec, succ);
        var proof = new Proof(new Name("Simple"), s, TacletForTests.initConfig());
        applyRule("assignment",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel(), false),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println("After assignment:\n" + proof.openGoals().head().sequent());
        applyRule("ifElseSplit",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel(), false),
            proof);
        assertEquals(2, proof.openGoals().size());
        System.out.println("After ifElseSplit:\n" + proof.openGoals().head().sequent());
        System.out.println(proof.openGoals().get(1).sequent());

        // Sub goal 1
        applyRule("emptyBlock",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel().down(1), false),
            proof);
        assertEquals(2, proof.openGoals().size());
        System.out.println("After emptyBlock:\n" + proof.openGoals().head().sequent());
        System.out.println(proof.openGoals().get(1).sequent());
        applyRule("assignment",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel().down(1), false),
            proof);
        assertEquals(2, proof.openGoals().size());
        System.out.println("After assignment:\n" + proof.openGoals().head().sequent());
        System.out.println(proof.openGoals().get(1).sequent());
        applyRule("emptyModality",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel().down(1).down(1), false),
            proof);
        assertEquals(2, proof.openGoals().size());
        System.out.println("After emptyModality:\n" + proof.openGoals().head().sequent());
        System.out.println(proof.openGoals().get(1).sequent());
        applyRule("simplifyUpdate2",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel(), false),
            proof);
        assertEquals(2, proof.openGoals().size());
        System.out.println("After simplifyUpdate2:\n" + proof.openGoals().head().sequent());
        System.out.println(proof.openGoals().get(1).sequent());
        applyRule("applyOnRigidFormula",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel(), false),
            proof);
        assertEquals(2, proof.openGoals().size());
        System.out.println("After applyOnRigidFormula:\n" + proof.openGoals().head().sequent());
        System.out.println(proof.openGoals().get(1).sequent());
        applyRule("applyOnPV",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel().down(0), false),
            proof);
        assertEquals(2, proof.openGoals().size());
        System.out.println("After applyOnPV:\n" + proof.openGoals().head().sequent());
        System.out.println(proof.openGoals().get(1).sequent());
        applyRule("simplifyUpdate1",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel().down(1), false),
            proof);
        assertEquals(2, proof.openGoals().size());
        System.out.println("After simplifyUpdate1:\n" + proof.openGoals().head().sequent());
        System.out.println(proof.openGoals().get(1).sequent());
        applyRule("eqClose",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel(), false),
            proof);
        assertEquals(2, proof.openGoals().size());
        System.out.println("After eqClose:\n" + proof.openGoals().head().sequent());
        System.out.println(proof.openGoals().get(1).sequent());
        applyRule("closeTrue",
            new PosInOccurrence(proof.openGoals().head().sequent().succedent().getFirst(),
                PosInTerm.getTopLevel(), false),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println("After closeTrue:\n" + proof.openGoals().head().sequent());

        // Subgoal 2
        applyRule("applyOnRigidFormula",
            new PosInOccurrence(proof.openGoals().head().sequent().antecedent().getFirst(),
                PosInTerm.getTopLevel(), true),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println("After applyOnRigidFormula:\n" + proof.openGoals().head().sequent());
        applyRule("applyOnPV",
            new PosInOccurrence(proof.openGoals().head().sequent().antecedent().getFirst(),
                PosInTerm.getTopLevel().down(0), true),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println("After applyOnPV:\n" + proof.openGoals().head().sequent());
        applyRule("simplifyUpdate1",
            new PosInOccurrence(proof.openGoals().head().sequent().antecedent().getFirst(),
                PosInTerm.getTopLevel().down(1), true),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println("After simplifyUpdate1:\n" + proof.openGoals().head().sequent());
        applyRule("bool_not_equal_2",
            new PosInOccurrence(proof.openGoals().head().sequent().antecedent().getFirst(),
                PosInTerm.getTopLevel(), true),
            proof);
        assertEquals(1, proof.openGoals().size());
        System.out.println("After bool_not_equal_2:\n" + proof.openGoals().head().sequent());
        applyRule("closeFalse",
            new PosInOccurrence(proof.openGoals().head().sequent().antecedent().getFirst(),
                PosInTerm.getTopLevel(), true),
            proof);
        assertEquals(0, proof.openGoals().size());
        try {
            ProofSaver.saveToFile(new File("if.proof"), proof);
        } catch (IOException e) {
            throw new RuntimeException(e);
        }
    }

    @Test
    public void testSwap() {
        // load
        TacletForTests.parse(new RustProfile());
        assert TacletForTests.services().getNamespaces().programVariables()
                .lookup(new Name("i")) != null;
        var services = TacletForTests.services();
        var intSort = services.getNamespaces().sorts().lookup("int");
        var intType = new KeYRustyType(intSort);
        var i_old = new ProgramVariable(new Name("i_old"), intSort, intType);
        var j_old = new ProgramVariable(new Name("j_old"), intSort, intType);
        TacletForTests.services().getNamespaces().programVariables().add(i_old);
        TacletForTests.services().getNamespaces().programVariables().add(j_old);

        var t = TacletForTests.parseTerm(
            "i=i_old & j=j_old -> \\<{i = i + j; j = i - j; i = i - j; 1u32}\\>(i = j_old & j = i_old)");
        System.out.println(t);


        Semisequent succ = new Semisequent(new SequentFormula(t));
        Sequent s = Sequent.createSuccSequent(succ);
        Proof p = new Proof("FirstProof", TacletForTests.initConfig());
        p.setRoot(new Node(p, s));

        p.getRoot().sequent().succedent().getFirst().formula();
        // continue manual proof like for example in TestApplyTaclet
    }

    @Test
    public void testRenamingProgramElementProperty() {
        TacletForTests.clear();
        TacletForTests.parse(new RustProfile());
        // seems like you must always give a type when using let
        var t1 = TacletForTests.parseTerm(
            "\\<{ let i: u32 = 5u32; 1u32 }\\>TRUE");
        var t2 = TacletForTests.parseTerm(
            "\\<{ let j: u32 = 5u32; 1u32 }\\>TRUE");

        var program1 = ((Modality) t1.op()).program().program();
        var program2 = ((Modality) t2.op()).program().program();

        assertTrue(
            RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(program1, program2,
                new NameAbstractionTable()));

        // Test 2
        var t3 = TacletForTests.parseTerm(
            "\\<{ 1u32 < 2u32 }\\>TRUE");
        var t4 = TacletForTests.parseTerm(
            "\\<{ 1u32 > 2u32 }\\>TRUE");

        var program3 = ((Modality) t3.op()).program().program();
        var program4 = ((Modality) t4.op()).program().program();

        assertFalse(
            RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(program3, program4,
                new NameAbstractionTable()));

        // Test 3
        var t5 = TacletForTests.parseTerm("\\<{ i += 5u32 }\\>TRUE");
        var t6 = TacletForTests.parseTerm("\\<{ i -= 5u32 }\\>TRUE");

        var program5 = ((Modality) t5.op()).program().program();
        var program6 = ((Modality) t6.op()).program().program();

        // This passes as += and -= are not considered as different operations in the property as of
        // now
        // and the PV i is the one defined in testrules.key and therefore equals returns true.
        // This currently does not work when using the let statement to introduce i.
        assertTrue(
            RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(program5, program6,
                new NameAbstractionTable()));

        // Test 4
        var t7 = TacletForTests.parseTerm(
            "\\<{ let mut i: u32 = 0u32; let mut j: u32 = 1u32; i = 2u32; j = i; 1u32}\\>TRUE");
        var t8 = TacletForTests.parseTerm(
            "\\<{ let mut i: u32 = 0u32; let mut k: u32 = 1u32; i = 2u32; k = i; 1u32}\\>TRUE");

        var program7 = ((Modality) t7.op()).program().program();
        var program8 = ((Modality) t8.op()).program().program();

        // assertTrue(
        // RENAMING_PROGRAM_ELEMENT_PROPERTY.equalsModThisProperty(program7, program8,
        // new NameAbstractionTable()));
    }
}
