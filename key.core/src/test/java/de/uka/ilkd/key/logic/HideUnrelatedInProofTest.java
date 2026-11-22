/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.logic;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import de.uka.ilkd.key.control.KeYEnvironment;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.proof.BuiltInRuleAppIndex;
import de.uka.ilkd.key.proof.BuiltInRuleIndex;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TacletIndexKit;
import de.uka.ilkd.key.proof.calculus.JavaDLSequentKit;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.PosTacletApp;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.util.HelperClassForTests;

import org.key_project.logic.Name;
import org.key_project.logic.PosInTerm;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.junit.jupiter.api.Test;

import static org.assertj.core.api.Assertions.assertThat;

/**
 * Verifies the rule-application mechanics of the "hide unrelated formulas" feature against a real
 * proof with the standard JavaDL rule set: {@code hide_left} / {@code hide_right} resolve, applying
 * them to the non-kept formulae of a goal removes exactly those and introduces a goal-local
 * {@code insert_hidden} rule (the undo path).
 */
class HideUnrelatedInProofTest {

    @Test
    void hideApplicationKeepsOnlyRelatedFormulas() throws Exception {
        KeYEnvironment<?> env = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
            HelperClassForTests.DUMMY_KEY_FILE, null, null, null, true);
        // a fresh proof over a deep copy of the loaded (full JavaDL) init config allows setting a
        // custom root; the copy also avoids the services-ownership conflict between two proofs
        Proof proof = new Proof("HideUnrelatedTest",
            env.getLoadedProof().getInitConfig().deepCopy());

        // formulas of the theory: imp(true,true) and not(true) share the subterm "true",
        // false does not
        TermFactory tf = proof.getServices().getTermBuilder().tf();
        JTerm jtrue = tf.createTerm(Junctor.TRUE);
        JTerm jfalse = tf.createTerm(Junctor.FALSE);
        JTerm imp = tf.createTerm(Junctor.IMP, jtrue, jtrue);
        JTerm not = tf.createTerm(Junctor.NOT, jtrue);
        SequentFormula sfImp = new SequentFormula(imp);
        SequentFormula sfNot = new SequentFormula(not);
        SequentFormula sfFalse = new SequentFormula(jfalse);
        Sequent seq =
            JavaDLSequentKit.createSuccSequent(ImmutableList.of(sfImp, sfNot, sfFalse));

        Node root = new Node(proof, seq);
        proof.setRoot(root);
        Goal goal = new Goal(root, TacletIndexKit.getKit().createTacletIndex(),
            new BuiltInRuleAppIndex(new BuiltInRuleIndex()), proof.getServices());

        Optional<Set<SequentFormula>> kept =
            RelatedFormulas.computeKeptFormulas(seq, jtrue, sfImp);
        assertThat(kept).isPresent();
        assertThat(kept.orElseThrow()).containsExactlyInAnyOrder(sfImp, sfNot);
        assertThat(RelatedFormulas.hidesNothing(seq, kept.orElseThrow())).isFalse();

        // hide every non-kept formula exactly like the GUI action does
        Goal current = goal;
        for (SequentFormula sf : seq.succedent()) {
            if (!kept.orElseThrow().contains(sf)) {
                current = applyHide(current, proof, sf, false);
            }
        }

        // the resulting goal shows exactly the related formulae ...
        List<SequentFormula> shown = new ArrayList<>();
        for (SequentFormula sf : current.sequent().succedent()) {
            shown.add(sf);
        }
        assertThat(shown).containsExactlyInAnyOrder(sfImp, sfNot);

        // ... and an insert_hidden rule provides the undo path
        List<String> localRules = new ArrayList<>();
        for (var app : current.node().getLocalIntroducedRules()) {
            localRules.add(app.taclet().name().toString());
        }
        assertThat(localRules).anyMatch(name -> name.startsWith("insert_hidden"));
    }

    /**
     * Applies {@code hide_left} / {@code hide_right} to the given formula of the goal and returns
     * the resulting goal. Mirrors the action of {@code HideUnrelatedExtension} (formerly
     * {@code SMTFocusResults.focus}).
     */
    private Goal applyHide(Goal current, Proof proof, SequentFormula sf, boolean inAntec) {
        FindTaclet hideTaclet = (FindTaclet) proof.getInitConfig()
                .lookupActiveTaclet(new Name(inAntec ? "hide_left" : "hide_right"));
        assertThat(hideTaclet).as("hide_* rule must be available").isNotNull();
        SchemaVariable schema = hideTaclet.collectSchemaVars().iterator().next();
        var services = proof.getServices();
        TacletApp app = PosTacletApp.createPosTacletApp(hideTaclet, new MatchConditions(),
            new PosInOccurrence(sf, PosInTerm.getTopLevel(), inAntec), services);
        app = app.addCheckedInstantiation(schema, (JTerm) sf.formula(), services, true);
        return current.apply(app).iterator().next();
    }
}
