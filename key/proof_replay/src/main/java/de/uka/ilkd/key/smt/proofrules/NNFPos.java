package de.uka.ilkd.key.smt.proofrules;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.macros.LimitedRulesMacro;
import de.uka.ilkd.key.macros.RuleCategories;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.smt.ReplayTools;
import de.uka.ilkd.key.smt.ReplayVisitor;
import de.uka.ilkd.key.smt.SMTProofParser.ProofsexprContext;

import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class NNFPos extends ProofRule {
    public NNFPos(Services services, Goal goal, ReplayVisitor replayVisitor) {
        super(services, goal, replayVisitor);
    }

    @Override
    public Goal replay(ProofsexprContext ctx) {
        Term antecedent = extractRuleAntecedents(ctx);
        TacletApp cutApp = ReplayTools.createCutApp(goal, antecedent);
        List<Goal> goals = ReplayTools.applyInteractive(goal, cutApp).toList();
        Goal left = goals.get(1);

        // currently we run auto mode for converting to nnf
        runAutoModeNNFPos(left, 1000);
        ////////////////////////////////////////////////////////////////////////////////////////////
        goal = goals.get(0);
        replayRightSideHelper(ctx);
        return goal;
    }

    // specialized auto mode with the quantifier distribution rule tailored to this use case
    public static void runAutoModeNNFPos(Goal goal, int steps) {
        Set<String> admittedRules = new HashSet<>();
        admittedRules.addAll(Arrays.asList(RuleCategories.PROPOSITIONAL_RULES));
        admittedRules.addAll(Arrays.asList(RuleCategories.FIRST_ORDER_RULES));
        admittedRules.addAll(Arrays.asList(RuleCategories.BOOLEAN_RULES));
        // NOTE: rules have to be in a rule set for this to work!
        admittedRules.add("distribute_all_equiv");
        LimitedRulesMacro macro = new LimitedRulesMacro(steps, admittedRules);
        try {
            macro.applyTo(null, goal.node(), null, null);
        } catch (Exception e) {
            e.printStackTrace();
        }
    }

}
