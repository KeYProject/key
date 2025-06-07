/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.strategy.*;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.symbolic_execution.util.SymbolicExecutionUtil;

import org.key_project.logic.Name;
import org.key_project.prover.proof.ProofGoal;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.instantiation.AssumesFormulaInstantiation;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.strategy.costbased.MutableState;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.prover.strategy.costbased.RuleAppCost;
import org.key_project.prover.strategy.costbased.TopRuleAppCost;
import org.key_project.prover.strategy.costbased.feature.Feature;

import org.jspecify.annotations.NonNull;

/**
 * {@link Strategy} used to simplify {@link JTerm}s in side proofs.
 *
 * @author Martin Hentschel
 */
public class SimplifyTermStrategy extends JavaCardDLStrategy {
    /**
     * The {@link Name} of the side proof {@link Strategy}.
     */
    public static final Name name = new Name("Simplify Term Strategy");

    /**
     * Constructor.
     *
     * @param proof The proof.
     * @param sp The {@link StrategyProperties} to use.
     */
    private SimplifyTermStrategy(Proof proof, StrategyProperties sp) {
        super(proof, sp);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public @NonNull Name name() {
        return name;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    protected Feature setupApprovalF() {
        Feature superFeature = super.setupApprovalF();
        Feature labelFeature = new Feature() {
            @Override
            public <Goal extends ProofGoal<@NonNull Goal>> RuleAppCost computeCost(RuleApp app,
                    PosInOccurrence pos, Goal goal, MutableState mState) {
                boolean hasLabel = false;
                if (pos != null && app instanceof TacletApp) {
                    JTerm findTerm = (JTerm) pos.subTerm();
                    if (!findTerm.containsLabel(SymbolicExecutionUtil.RESULT_LABEL)) {
                        // Term with result label is not used in find term and thus is not allowed
                        // to be used in an assumes clause
                        TacletApp ta = (TacletApp) app;
                        if (ta.assumesFormulaInstantiations() != null) {
                            for (AssumesFormulaInstantiation ifi : ta
                                    .assumesFormulaInstantiations()) {
                                if (((JTerm) ifi.getSequentFormula().formula())
                                        .containsLabel(SymbolicExecutionUtil.RESULT_LABEL)) {
                                    hasLabel = true;
                                }
                            }
                        }
                    }
                }
                return hasLabel ? TopRuleAppCost.INSTANCE : NumberRuleAppCost.create(0);
            }
        };
        // The label feature ensures that Taclets mapping an assumes to a Term with a result label
        // are only applicable if also a Term with the result label is used in the find clause
        return add(labelFeature, superFeature);
    }

    /**
     * The {@link StrategyFactory} to create instances of {@link SimplifyTermStrategy}.
     *
     * @author Martin Hentschel
     */
    public static class Factory implements StrategyFactory {
        /**
         * {@inheritDoc}
         */
        @Override
        public Strategy<Goal> create(Proof proof, StrategyProperties sp) {
            return new SimplifyTermStrategy(proof, sp);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public @NonNull Name name() {
            return name;
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public StrategySettingsDefinition getSettingsDefinition() {
            return JavaProfile.DEFAULT.getSettingsDefinition();
        }
    }
}
