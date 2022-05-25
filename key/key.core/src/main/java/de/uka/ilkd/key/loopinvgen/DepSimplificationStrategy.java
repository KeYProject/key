package de.uka.ilkd.key.loopinvgen;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.JavaCardDLStrategy;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.feature.*;
import de.uka.ilkd.key.strategy.termProjection.FocusFormulaProjection;

public class DepSimplificationStrategy extends JavaCardDLStrategy {

    public DepSimplificationStrategy(Proof proof, StrategyProperties strategyProperties) {
        super(proof, strategyProperties);
    }

    @Override
    protected Feature setupGlobalF(Feature dispatcher) {
        Feature global = super.setupGlobalF(dispatcher);
        final RuleSetDispatchFeature d = new RuleSetDispatchFeature();

        bindRuleSet(d, "simplify_ENLARGING", inftyConst());
        bindRuleSet(d, "simplify_enlarging", inftyConst());

        bindRuleSet(d, "dep_replace_known", inftyConst());//EqNonDuplicateAppFeature

        Feature depth = applyTF(FocusFormulaProjection.INSTANCE, rec(any(), longTermConst(1)));

        bindRuleSet(d, "dep_pred_unroll_fixed_bounds", inftyConst());//longConst(0));
        bindRuleSet(d, "dep_pred_known", inftyConst());//+100
        bindRuleSet(d, "dep_pred_known_2", inftyConst());//+100
        bindRuleSet(d, "dep_pred_known_2b", inftyConst());
        //bindRuleSet(d, "dep_pred_known_3", add(noDoubleMinus,longConst(-500)));//-500
        bindRuleSet(d, "saturate_dep_locset_relations_def", inftyConst());//add(noDoubleMinus,NonDuplicateAppModPositionFeature.INSTANCE, ScaleFeature.createScaled(depth, 1000), longConst(300)));

        return add(d, global);
    }
}
