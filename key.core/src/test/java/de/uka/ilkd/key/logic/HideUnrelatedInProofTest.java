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
import de.uka.ilkd.key.rule.NoPosTacletApp;
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
 * them to the non-kept formulae (on both sides of the sequent, chained) removes exactly those and
 * introduces goal-local {@code insert_hidden} rules which fully restore the sequent (the undo
 * path).
 */
class HideUnrelatedInProofTest {

    @Test
    void hideApplicationKeepsOnlyRelatedFormulasAndIsUndone() throws Exception {
        KeYEnvironment<?> env = KeYEnvironment.load(JavaProfile.getDefaultInstance(),
            HelperClassForTests.DUMMY_KEY_FILE, null, null, null, true);
        // a fresh proof over a deep copy of the loaded (full JavaDL) init config allows setting a
        // custom root; the copy also avoids the services-ownership conflict between two proofs
        Proof proof = new Proof("HideUnrelatedTest",
            env.getLoadedProof().getInitConfig().deepCopy());

        // formulas of the theory: imp(true,true) and not(true) share the subterm "true",
        // false and not(false) do not
        TermFactory tf = proof.getServices().getTermBuilder().tf();
        JTerm jtrue = tf.createTerm(Junctor.TRUE);
        JTerm jfalse = tf.createTerm(Junctor.FALSE);
        JTerm imp = tf.createTerm(Junctor.IMP, jtrue, jtrue);
        JTerm notTrue = tf.createTerm(Junctor.NOT, jtrue);
        JTerm notFalse = tf.createTerm(Junctor.NOT, jfalse);
        SequentFormula sfImp = new SequentFormula(imp);
        SequentFormula sfNotTrue = new SequentFormula(notTrue);
        SequentFormula sfFalse = new SequentFormula(jfalse);
        SequentFormula sfNotFalse = new SequentFormula(notFalse);
        Sequent seq = JavaDLSequentKit.createSequent(ImmutableList.of(sfNotFalse),
            ImmutableList.of(sfImp, sfNotTrue, sfFalse, sfNotFalse));

        Node root = new Node(proof, seq);
        proof.setRoot(root);
        Goal goal = new Goal(root, TacletIndexKit.getKit().createTacletIndex(),
            new BuiltInRuleAppIndex(new BuiltInRuleIndex()), proof.getServices());

        Optional<Set<SequentFormula>> kept = RelatedFormulas.computeKeptFormulas(seq, jtrue, sfImp);
        assertThat(kept).isPresent();
        assertThat(kept.orElseThrow()).containsExactlyInAnyOrder(sfImp, sfNotTrue);

        // hide every non-kept formula on both sides, chained exactly like the GUI action does
        Goal current = goal;
        for (SequentFormula sf : seq.antecedent()) {
            if (!kept.orElseThrow().contains(sf)) {
                current = applyHide(current, proof, sf, true);
            }
        }
        for (SequentFormula sf : seq.succedent()) {
            if (!kept.orElseThrow().contains(sf)) {
                current = applyHide(current, proof, sf, false);
            }
        }

        // the resulting goal shows exactly the related formulae on both sides ...
        assertThat(sequentFormulas(current.sequent().antecedent())).isEmpty();
        assertThat(sequentFormulas(current.sequent().succedent()))
                .containsExactlyInAnyOrder(sfImp, sfNotTrue);

        // ... and the undo path exists: every generated insert_hidden rule is visible in the
        // final goal's taclet index (which accumulates the ancestor goals' local rules), and
        // re-applying them restores the full sequent
        Set<NoPosTacletApp> introduced = current.ruleAppIndex().tacletIndex().allNoPosTacletApps()
                .stream().filter(app -> app.taclet().name().toString().startsWith("insert_hidden"))
                .collect(java.util.stream.Collectors.toUnmodifiableSet());
        assertThat(introduced).hasSize(3);

        for (NoPosTacletApp app : introduced) {
            current = current.apply(app).iterator().next();
        }

        // the original sequent is fully restored
        assertThat(sequentFormulas(current.sequent().antecedent())).containsExactly(sfNotFalse);
        assertThat(sequentFormulas(current.sequent().succedent()))
                .containsExactlyInAnyOrder(sfImp, sfNotTrue, sfFalse, sfNotFalse);
    }

    private static List<SequentFormula> sequentFormulas(Iterable<SequentFormula> semisequent) {
        List<SequentFormula> result = new ArrayList<>();
        semisequent.forEach(result::add);
        return result;
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
