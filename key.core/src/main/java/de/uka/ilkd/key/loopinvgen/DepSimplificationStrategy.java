/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.definition.StrategySettingsDefinition;
import de.uka.ilkd.key.strategy.feature.*;

import org.key_project.logic.Name;

public class DepSimplificationStrategy extends JavaCardDLStrategy {

    private static final String DEPENDENCY_SIMPLIFICATION_STRATEGY =
        "DepenendencySimplificationStrategy";

    public DepSimplificationStrategy(Proof proof, StrategyProperties strategyProperties) {
        super(proof, strategyProperties);
    }

    @Override
    public Name name() {
        return new Name(DEPENDENCY_SIMPLIFICATION_STRATEGY);
    }

    @Override
    protected Feature setupGlobalF(Feature dispatcher) {
        Feature global = super.setupGlobalF(dispatcher);
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();

        bindRuleSet(d, "simplify_ENLARGING", inftyConst());
        bindRuleSet(d, "simplify_enlarging", inftyConst());

        bindRuleSet(d, "dep_replace_known", inftyConst());// EqNonDuplicateAppFeature

        // Feature depth = applyTF(FocusFormulaProjection.INSTANCE, rec(any(), longTermConst(1)));

        bindRuleSet(d, "dep_pred_unroll_fixed_bounds", inftyConst());// longConst(0));
        bindRuleSet(d, "dep_pred_known", inftyConst());// +100
        bindRuleSet(d, "dep_pred_known_2", inftyConst());// +100
        bindRuleSet(d, "dep_pred_known_2b", inftyConst());
        bindRuleSet(d, "dep_pred_known_3", inftyConst());// add(noDoubleMinus,longConst(-500)));//-500
        bindRuleSet(d, "saturate_dep_locset_relations_def", inftyConst());// add(noDoubleMinus,NonDuplicateAppModPositionFeature.INSTANCE,
                                                                          // ScaleFeature.createScaled(depth,
                                                                          // 1000),
                                                                          // longConst(300)));

        bindRuleSet(d, "relaxedAccumulation", inftyConst());

        return add(d, global);
    }

    public static class Factory implements StrategyFactory {
        /**
         * {@inheritDoc}
         */
        @Override
        public Strategy create(Proof proof, StrategyProperties sp) {
            return new DepSimplificationStrategy(proof, sp);
        }

        /**
         * {@inheritDoc}
         */
        @Override
        public Name name() {
            return new Name(DEPENDENCY_SIMPLIFICATION_STRATEGY);
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
