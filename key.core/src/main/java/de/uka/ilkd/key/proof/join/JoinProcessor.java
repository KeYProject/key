/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.join;

import java.util.Collection;
import java.util.Comparator;
import java.util.LinkedList;
import java.util.TreeSet;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.delayedcut.DelayedCut;
import de.uka.ilkd.key.proof.delayedcut.DelayedCutProcessor;
import de.uka.ilkd.key.proof.delayedcut.NodeGoalPair;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.PosTacletApp;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.proof.rulefilter.TacletFilter;
import org.key_project.prover.rules.Taclet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Semisequent;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

/**
 * <p>
 * The JoinProcessor is responsible for executing the joining. Let N1 and N2 be the nodes which
 * should be joined and let N be the node where the branches of N1 and N2 join. Further let F be the
 * given decision formula. Then the following steps are applied:
 * </p>
 *
 * <ol>
 * <li>Based on the formulas contained in n1 and n2 and the given decision formula F, a further
 * Formula F' created which is used for the second step.</li>
 * <li>Based on F' the delayed-cut mechanism is applied on N.</li>
 * <li>The created update in F' is simplified.</li>
 * </ol>
 *
 * <p>
 * The delayed-cut mechanism prunes the proof at a common predecessor, introduces a cut for a
 * defined decision predicate, and replays the existing proof afterward. Note that by the means of
 * this approach, there are no non-local rule applications in the resulting proof. This avoids
 * certain complications arising from a "defocusing" join rule that establishes a link between a
 * join node and its partner. However, replaying does not work in every case, for instance if a
 * subtree of the common parent introduces new symbols.
 * </p>
 *
 * @author Benjamin Niedermann
 * @see DelayedCutProcessor
 */
public class JoinProcessor implements Runnable {
    private boolean used = false;
    private final Proof proof;
    private final Services services;
    private final ProspectivePartner partner;
    private final LinkedList<Listener> listeners = new LinkedList<>();
    private static final String HIDE_RIGHT_TACLET = "hide_right";
    private static final String OR_RIGHT_TACLET = "orRight";
    public static final String[] SIMPLIFY_UPDATE =
        { "simplifyIfThenElseUpdate1", "simplifyIfThenElseUpdate2", "simplifyIfThenElseUpdate3" };

    public interface Listener {
        void exceptionWhileJoining(Throwable e);

        void endOfJoining(ImmutableList<Goal> goals);
    }

    public JoinProcessor(ProspectivePartner partner, Proof proof) {
        super();
        this.proof = proof;
        this.services = proof.getServices();
        this.partner = partner;
    }

    public void join() {
        if (used) {
            throw new IllegalStateException("Every instance can only be used once.");
        }
        used = true;
        processJoin();

    }

    public void addListener(Listener listener) {
        listeners.add(listener);
    }

    private void processJoin() {

        JTerm cutFormula = createCutFormula();

        DelayedCutProcessor cutProcessor = new DelayedCutProcessor(proof, partner.getCommonParent(),
            cutFormula, DelayedCut.DECISION_PREDICATE_IN_ANTECEDENT);

        DelayedCut cut = cutProcessor.cut();

        Goal result = hide(cut.getRemainingGoal());

        result = simplifyUpdate(result, cut);

        orRight(result);

        ImmutableList<Goal> list = ImmutableSLList.nil();

        for (NodeGoalPair pair : cut.getGoalsAfterUncovering()) {
            if (pair.node == partner.getNode(0) || pair.node == partner.getNode(1)) {
                list = list.append(pair.goal);
            }
        }

        for (Listener listener : listeners) {
            listener.endOfJoining(list);
        }
    }

    private void orRight(Goal goal) {
        SequentFormula sf = goal.sequent().succedent().get(0);
        PosInOccurrence pio =
            new PosInOccurrence(sf, PosInTerm.getTopLevel(), false);
        apply(new String[] { OR_RIGHT_TACLET }, goal, pio);

    }

    private SequentFormula findFormula(Sequent sequent, JTerm content,
            boolean antecedent) {
        for (SequentFormula sf : (antecedent ? sequent.antecedent()
                : sequent.succedent())) {
            if (sf.formula().equals(content)) {
                return sf;
            }
        }
        return null;
    }

    private Goal simplifyUpdate(Goal goal, DelayedCut cut) {

        SequentFormula sf =
            findFormula(goal.sequent(), cut.getFormula(), false);

        PosInOccurrence pio =
            new PosInOccurrence(sf, PosInTerm.getTopLevel().down(0), false);
        Goal result = apply(SIMPLIFY_UPDATE, goal, pio).head();

        return result == null ? goal : result;
    }

    /**
     * Applies one of the given taclets if this possible otherwise an exception is thrown.
     */
    private ImmutableList<Goal> apply(final String[] tacletNames, Goal goal,
            PosInOccurrence pio) {

        TacletFilter filter = new TacletFilter() {

            @Override
            protected boolean filter(Taclet taclet) {
                for (String tacletName : tacletNames) {
                    if (taclet.name().toString().equals(tacletName)) {
                        return true;
                    }
                }
                return false;
            }

        };
        ImmutableList<NoPosTacletApp> apps =
            goal.ruleAppIndex().getFindTaclet(filter, pio);

        if (apps.isEmpty()) {
            return null;

        }
        NoPosTacletApp app = apps.head();

        PosTacletApp app2 = app.setPosInOccurrence(pio, services);
        return goal.apply(app2);
    }

    private Goal hide(Goal goal) {
        if (partner.getFormulaForHiding() == null) {
            return goal;
        }
        int index = goal.sequent().formulaNumberInSequent(false, partner.getFormulaForHiding());
        PosInOccurrence pio =
            PosInOccurrence.findInSequent(goal.sequent(), index,
                PosInTerm.getTopLevel());
        return apply(new String[] { HIDE_RIGHT_TACLET }, goal, pio).head();

    }

    private JTerm createCutFormula() {
        JTerm ifElseTerm = buildIfElseTerm();
        JTerm phi = createPhi();
        return services.getTermBuilder().or(ifElseTerm, phi);
    }

    private JTerm buildIfElseTerm() {
        JTerm thenTerm =
            services.getTermBuilder().apply(partner.getUpdate(0), partner.getCommonFormula(), null);
        JTerm elseTerm =
            services.getTermBuilder().apply(partner.getUpdate(1), partner.getCommonFormula(), null);

        return services.getTermBuilder().ife(partner.getCommonPredicate(), thenTerm, elseTerm);

    }

    private JTerm createPhi() {
        Collection<JTerm> commonDelta = computeCommonFormulas(partner.getSequent(0).succedent(),
            partner.getSequent(1).succedent(), partner.getCommonFormula());
        Collection<JTerm> commonGamma = computeCommonFormulas(partner.getSequent(0).antecedent(),
            partner.getSequent(1).antecedent(), partner.getCommonFormula());
        Collection<JTerm> delta1 = computeDifference(partner.getSequent(0).succedent(), commonDelta,
            (JTerm) partner.getFormula(0).formula());
        Collection<JTerm> delta2 = computeDifference(partner.getSequent(1).succedent(), commonDelta,
            (JTerm) partner.getFormula(1).formula());

        Collection<JTerm> gamma1 =
            computeDifference(partner.getSequent(0).antecedent(), commonGamma, null);
        Collection<JTerm> gamma2 =
            computeDifference(partner.getSequent(1).antecedent(), commonGamma, null);

        Collection<JTerm> constrainedGamma1 =
            createConstrainedTerms(gamma1, partner.getCommonPredicate(), true);
        Collection<JTerm> constrainedGamma2 = createConstrainedTerms(gamma2,
            services.getTermBuilder().not(partner.getCommonPredicate()), true);

        Collection<JTerm> constrainedDelta1 =
            createConstrainedTerms(delta1, partner.getCommonPredicate(), false);
        Collection<JTerm> constrainedDelta2 = createConstrainedTerms(delta2,
            services.getTermBuilder().not(partner.getCommonPredicate()), false);

        JTerm phi = services.getTermBuilder().ff();
        phi = createDisjunction(phi, commonGamma, true);
        phi = createDisjunction(phi, constrainedGamma1, true);
        phi = createDisjunction(phi, constrainedGamma2, true);

        phi = createDisjunction(phi, commonDelta, false);
        phi = createDisjunction(phi, constrainedDelta1, false);
        phi = createDisjunction(phi, constrainedDelta2, false);

        return phi;
    }

    private JTerm createDisjunction(JTerm seed, Collection<JTerm> formulas, boolean needNot) {
        for (JTerm formula : formulas) {
            if (needNot) {
                seed = services.getTermBuilder().or(seed, services.getTermBuilder().not(formula));
            } else {
                seed = services.getTermBuilder().or(seed, formula);
            }
        }
        return seed;
    }

    private Collection<JTerm> createConstrainedTerms(Collection<JTerm> terms, JTerm predicate,
            boolean gamma) {
        Collection<JTerm> result = new LinkedList<>();
        for (JTerm term : terms) {
            if (gamma) {
                result.add(services.getTermBuilder().imp(predicate, term));
            } else {
                result.add(services.getTermBuilder().and(predicate, term));
            }
        }
        return result;
    }

    private Collection<JTerm> computeCommonFormulas(Semisequent s1, Semisequent s2, JTerm exclude) {
        TreeSet<JTerm> formulas1 = createTree(s1, exclude);
        TreeSet<JTerm> result = createTree();
        for (SequentFormula sf : s2) {
            if (formulas1.contains(sf.formula())) {
                result.add((JTerm) sf.formula());
            }
        }
        return result;
    }

    private Collection<JTerm> computeDifference(Semisequent s, Collection<JTerm> excludeSet,
            JTerm exclude) {
        LinkedList<JTerm> result = new LinkedList<>();
        for (SequentFormula sf : s) {
            if (sf.formula() != exclude && !excludeSet.contains(sf.formula())) {
                result.add((JTerm) sf.formula());
            }
        }
        return result;
    }

    private TreeSet<JTerm> createTree(Semisequent semisequent, JTerm exclude) {
        TreeSet<JTerm> set = createTree();
        for (SequentFormula sf : semisequent) {
            if (sf.formula() != exclude) {
                set.add((JTerm) sf.formula());
            }
        }
        return set;
    }

    private TreeSet<JTerm> createTree() {
        return new TreeSet<>(Comparator.comparingInt(JTerm::serialNumber));
    }

    @Override
    public void run() {
        try {
            join();
        } catch (Throwable e) {
            for (Listener listener : listeners) {
                listener.exceptionWhileJoining(e);
            }
        }
    }

}
