/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */

package de.uka.ilkd.key.macros;

import java.util.*;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Modality;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.OneStepSimplifier;
import de.uka.ilkd.key.rule.Rule;
import de.uka.ilkd.key.rule.RuleApp;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.strategy.NumberRuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCost;
import de.uka.ilkd.key.strategy.RuleAppCostCollector;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.TopRuleAppCost;

import org.key_project.util.LRUCache;

public class AutoPilotPrepareProofMacro extends StrategyProofMacro {

    private static final String[] ADMITTED_RULES = {
        "orRight", "impRight", "close", "andRight"
    };

    private static final Set<String> ADMITTED_RULES_SET = asSet(ADMITTED_RULES);

    private static final Name NON_HUMAN_INTERACTION_RULESET = new Name("notHumanReadable");

    public AutoPilotPrepareProofMacro() { super(); }

    @Override
    public String getName() {
        return "Auto Pilot (Preparation Only)";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getDescription() {
        return "<html><ol><li>Finish symbolic execution" +
            "<li>Separate proof obligations" +
            "<li>Expand invariant definitions</ol>";
    }

    @Override
    public String getScriptCommandName() {
        return "autopilot-prep";
    }

    /*
     * convert a string array to a set of strings
     */
    protected static Set<String> asSet(String[] strings) {
        return Collections.unmodifiableSet(new LinkedHashSet<String>(Arrays.asList(strings)));
    }

    /*
     * Checks if a rule is marked as not suited for interaction.
     */
    private static boolean isNonHumanInteractionTagged(Rule rule) {
        return isInRuleSet(rule, NON_HUMAN_INTERACTION_RULESET);
    }

    private static boolean isInRuleSet(Rule rule, Name ruleSetName) {
        if (rule instanceof Taclet) {
            Taclet taclet = (Taclet) rule;
            for (RuleSet rs : taclet.getRuleSets()) {
                if (ruleSetName.equals(rs.name()))
                    return true;
            }
        }
        return false;
    }

    private static class AutoPilotStrategy implements Strategy {

        private static final Name NAME = new Name("Autopilot filter strategy");
        private final Strategy delegate;
        private final Map<Term, Boolean> termHasModalityCache = new LRUCache<>(2000);

        // Caching more than one sequent does not help since autopilot rarely revisits nodes
        private Sequent sequentHasModality = null;
        private boolean sequentHasModalityValue = false;

        public AutoPilotStrategy(Proof proof, PosInOccurrence posInOcc) {
            this.delegate = proof.getActiveStrategy();
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            return computeCost(app, pio, goal) != TopRuleAppCost.INSTANCE &&
            // Assumptions are normally not considered by the cost
            // computation, because they are normally not yet
            // instantiated when the costs are computed. Because the
            // application of a rule sometimes makes sense only if
            // the assumptions are instantiated in a particular way
            // (for instance equalities should not be applied on
            // themselves), we need to give the delegate the possiblity
            // to reject the application of a rule by calling
            // isApprovedApp. Otherwise, in particular equalities may
            // be applied on themselves.
                    delegate.isApprovedApp(app, pio, goal);
        }

        /*
         * find a modality term
         */
        private boolean termHasModality(Term term) {
            Boolean cached = termHasModalityCache.get(term);
            if (cached != null) {
                return cached;
            }

            // This is the faster comparison but rarely returns
            if (term.op() instanceof Modality) {
                return true;
            }

            var hasModality = false;
            for (Term sub : term.subs()) {
                if (termHasModality(sub)) {
                    hasModality = true;
                    break;
                }
            }

            termHasModalityCache.put(term, hasModality);
            return hasModality;
        }

        /*
         * find a modality term in a node
         */
        private boolean hasModality(Sequent sequent) {
            if (sequentHasModality == sequent) {
                return sequentHasModalityValue;
            }

            var result = false;
            for (SequentFormula sequentFormula : sequent) {
                if (termHasModality(sequentFormula.formula())) {
                    result = true;
                    break;
                }
            }

            sequentHasModality = sequent;
            sequentHasModalityValue = result;
            return result;
        }

        @Override
        public RuleAppCost computeCost(RuleApp app, PosInOccurrence pio, Goal goal) {

            Rule rule = app.rule();
            if (isNonHumanInteractionTagged(rule)) {
                return TopRuleAppCost.INSTANCE;
            }

            if (hasModality(goal.node().sequent())) {
                return delegate.computeCost(app, pio, goal);
            }

            String name = rule.name().toString();
            if (ADMITTED_RULES_SET.contains(name)) {
                return NumberRuleAppCost.getZeroCost();
            }

            // apply OSS to <inv>() calls.
            if (rule instanceof OneStepSimplifier) {
                Term target = pio.subTerm();
                if (target.op() instanceof UpdateApplication) {
                    Operator updatedOp = target.sub(1).op();
                    if (updatedOp instanceof ObserverFunction) {
                        return NumberRuleAppCost.getZeroCost();
                    }
                }
            }

            return TopRuleAppCost.INSTANCE;
        }

        @Override
        public void instantiateApp(RuleApp app, PosInOccurrence pio, Goal goal,
                RuleAppCostCollector collector) {
            delegate.instantiateApp(app, pio, goal, collector);
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }

    }

    @Override
    protected Strategy createStrategy(Proof proof, PosInOccurrence posInOcc) {
        return new AutoPilotStrategy(proof, posInOcc);
    }
}
