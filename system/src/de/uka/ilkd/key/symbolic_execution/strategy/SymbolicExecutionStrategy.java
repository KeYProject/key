package de.uka.ilkd.key.symbolic_execution.strategy;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.strategy.Strategy;
import de.uka.ilkd.key.strategy.StrategyFactory;
import de.uka.ilkd.key.strategy.StrategyProperties;
import de.uka.ilkd.key.strategy.feature.CountBranchFeature;
import de.uka.ilkd.key.strategy.feature.Feature;
import de.uka.ilkd.key.strategy.feature.RuleSetDispatchFeature;
import de.uka.ilkd.key.strategy.feature.ScaleFeature;

//TODO: Discuss settings and improve the code layout.
/**
 * Strategy tailored to VBT aimed symbolic execution.
 */
public class SymbolicExecutionStrategy extends VBTStrategy {

    public static final String VISUAL_DEBUGGER_SPLITTING_RULES_KEY = "VD_SPLITTING_RULES_KEY";
    public static final String VISUAL_DEBUGGER_WATCHPOINTS_KEY = "WATCHPOINTS_KEY";

    public static final String VISUAL_DEBUGGER_IN_UPDATE_AND_ASSUMES_KEY = "VD_IN_UPDATE_AND_ASSUMES_RULES_KEY";

    public static final String VISUAL_DEBUGGER_IN_INIT_PHASE_KEY = "VD_IN_INIT_PHASE_KEY";

    public static final String VISUAL_DEBUGGER_TRUE = "TRUE";

    public static final String VISUAL_DEBUGGER_FALSE = "FALSE";

    public static StrategyProperties getSymbolicExecutionStrategyProperties(
            boolean splittingRulesAllowed, boolean inUpdateAndAssumes,
            boolean inInitPhase, boolean quantifierInstantiationWithSplitting) { // , List<WatchPoint> watchpoints
        final StrategyProperties res = new StrategyProperties();
        res.setProperty(StrategyProperties.LOOP_OPTIONS_KEY,
                StrategyProperties.LOOP_EXPAND);
        res.setProperty(StrategyProperties.BLOCK_OPTIONS_KEY,
                StrategyProperties.BLOCK_EXPAND);
        res.setProperty(StrategyProperties.METHOD_OPTIONS_KEY,
                StrategyProperties.METHOD_EXPAND);
        res.setProperty(StrategyProperties.QUERY_OPTIONS_KEY,
                StrategyProperties.QUERY_OFF);
        res.setProperty(StrategyProperties.NON_LIN_ARITH_OPTIONS_KEY,
                StrategyProperties.NON_LIN_ARITH_DEF_OPS);
        res.setProperty(StrategyProperties.AUTO_INDUCTION_OPTIONS_KEY,
              StrategyProperties.AUTO_INDUCTION_OFF);
        res.setProperty(StrategyProperties.DEP_OPTIONS_KEY,
              StrategyProperties.DEP_OFF);
        res.setProperty(StrategyProperties.QUERYAXIOM_OPTIONS_KEY,
              StrategyProperties.QUERYAXIOM_OFF);
        res.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY,
              StrategyProperties.SPLITTING_DELAYED);
//        res.put(VISUAL_DEBUGGER_WATCHPOINTS_KEY, watchpoints);
//        res.setProperty(StrategyProperties.SPLITTING_OPTIONS_KEY,
//                StrategyProperties.SPLITTING_NORMAL);

        if (quantifierInstantiationWithSplitting) {
            res.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
                    StrategyProperties.QUANTIFIERS_INSTANTIATE);
        } else {
            res.setProperty(StrategyProperties.QUANTIFIERS_OPTIONS_KEY,
                    StrategyProperties.QUANTIFIERS_NON_SPLITTING_WITH_PROGS);
        }

        res.setProperty(VISUAL_DEBUGGER_SPLITTING_RULES_KEY,
                splittingRulesAllowed ? VISUAL_DEBUGGER_TRUE
                        : VISUAL_DEBUGGER_FALSE);

        res.setProperty(VISUAL_DEBUGGER_IN_UPDATE_AND_ASSUMES_KEY,
                inUpdateAndAssumes ? VISUAL_DEBUGGER_TRUE
                        : VISUAL_DEBUGGER_FALSE);

        res.setProperty(VISUAL_DEBUGGER_IN_INIT_PHASE_KEY,
                inInitPhase ? VISUAL_DEBUGGER_TRUE : VISUAL_DEBUGGER_FALSE);

        return res;
    }

    protected SymbolicExecutionStrategy(Proof p_proof, StrategyProperties props) { // ,List<WatchPoint> watchpoints

        super(p_proof, props, 0);

//        final boolean isSplittingAllowed = props.get(
//                VISUAL_DEBUGGER_SPLITTING_RULES_KEY).equals(
//                VISUAL_DEBUGGER_TRUE);
//
//        final boolean inUpdateAndAssumes = props.get(
//                VISUAL_DEBUGGER_IN_UPDATE_AND_ASSUMES_KEY).equals(
//                VISUAL_DEBUGGER_TRUE);
//
//        final boolean inInitPhase = props
//                .get(VISUAL_DEBUGGER_IN_INIT_PHASE_KEY).equals(
//                        VISUAL_DEBUGGER_TRUE);
        
        RuleSetDispatchFeature d = getCostComputationDispatcher();

//        bindRuleSet(d, "simplify_autoname", ifZero(BreakpointFeature.create(),
//                inftyConst(), longConst(0)));
//        bindRuleSet(d, "method_expand", ifZero(BreakpointFeature.create(),
//                inftyConst(), longConst(0)));
//        if (!inInitPhase) {
//            bindRuleSet(d, "simplify_autoname", ifZero(WatchPointFeature.create(watchpoints),
//                    inftyConst(), longConst(0)));
//        }
//        if (!inInitPhase) {
//            bindRuleSet(d, "method_expand", ifZero(WatchPointFeature.create(watchpoints),
//                    inftyConst(), longConst(0)));
       
//        }
        
        final Feature splitF = ScaleFeature.createScaled ( CountBranchFeature.INSTANCE, -400);
        bindRuleSet(d, "split_if", splitF); // The costs of rules in heuristic "split_if" is reduced at runtime by numberOfBranches * -400. The result is that rules of "split_if" preferred to "split_cond" and run and step into has the same behavior
        bindRuleSet(d, "instanceof_to_exists", inftyConst());

//        bindRuleSet(d, "split_cond", ifZero(LabelFeature.INSTANCE,
//                longConst(-3000), longConst(0)));

//        bindRuleSet(d, "beta", ifZero(LabelFeature.INSTANCE, longConst(-3000),
//                longConst(0)));

//        final NamespaceSet nss = p_proof.getNamespaces();

//        assert nss != null : "Rule set namespace not available.";

//        // FIXME: do not add it for each rule set add it as sum feature
//
//        final ImmutableList<Named> h = nss.ruleSets().allElements();
//
//        final Feature inUpdateFeature = InUpdateFeature.create(
//                isSplittingAllowed, inUpdateAndAssumes, inInitPhase);
//
//        for (Named aH : h) {
//            final String ruleSetName = aH.name().toString();
//            bindRuleSet(d, ruleSetName, ifZero(inUpdateFeature, inftyConst(),
//                    longConst(0)));
//        }
    }

    public Name name() {
        return new Name("DebuggerStrategy");
    }

    public static class Factory extends StrategyFactory {

        public Factory() {
        }

        public Strategy create(Proof p_proof,
                StrategyProperties strategyProperties) {

//            List<WatchPoint> watchpoints =  (List<WatchPoint>) strategyProperties
//                    .get(VISUAL_DEBUGGER_WATCHPOINTS_KEY);
            injectDebuggerDefaultOptionsIfUnset(strategyProperties);
            
            return new SymbolicExecutionStrategy(p_proof, strategyProperties); // ,watchpoints
        }

        private void injectDebuggerDefaultOptionsIfUnset(
                StrategyProperties props) {

            if (!props.containsKey(VISUAL_DEBUGGER_SPLITTING_RULES_KEY)) {
                props.put(VISUAL_DEBUGGER_SPLITTING_RULES_KEY,
                        VISUAL_DEBUGGER_TRUE);
            }

            if (!props.containsKey(VISUAL_DEBUGGER_IN_UPDATE_AND_ASSUMES_KEY)) {
                props.put(VISUAL_DEBUGGER_IN_UPDATE_AND_ASSUMES_KEY,
                        VISUAL_DEBUGGER_FALSE);
            }

            if (!props.containsKey(VISUAL_DEBUGGER_IN_INIT_PHASE_KEY)) {
                props.put(VISUAL_DEBUGGER_IN_INIT_PHASE_KEY,
                        VISUAL_DEBUGGER_TRUE);
            }
        }

        public Name name() {
            return new Name("DebuggerStrategy");
        }
    }
}
