/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import de.uka.ilkd.key.control.TermLabelVisibilityManager;
import de.uka.ilkd.key.logic.op.ObserverFunction;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.strategy.Strategy;
import org.jspecify.annotations.NonNull;
import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.prover.strategy.costbased.NumberRuleAppCost;
import org.key_project.util.Streams;
import org.key_project.util.java.StringUtil;

import java.io.IOException;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

/**
 * This macro is very restritive in which rules are allowed to be applied for symbolic
 * execution. No reasoning rules should ever be applied.
 *
 * @author mattias ulbrich
 */
public class SymbolicExecutionOnlyMacro extends StrategyProofMacro {

    private static final List<String> ADMITTED_RULES;
    private static final List<String> ADMITTED_RULE_SETS;
    static {
        try {
            ADMITTED_RULES = Arrays.asList(
                    Streams.toString(SymbolicExecutionOnlyMacro.class.getResourceAsStream("SymbolicExecutionOnlyMacro.admittedRules.txt")).split("\n"));
            ADMITTED_RULE_SETS = Arrays.asList(
                    Streams.toString(SymbolicExecutionOnlyMacro.class.getResourceAsStream("SymbolicExecutionOnlyMacro.admittedRuleSets.txt")).split("\n"));
        } catch (IOException e) {
            throw new RuntimeException("Failed to load admitted rules for symbolic execution macro.", e);
        }
    }

    @Override
    public String getName() {
        return "Symbolic Execution Only";
    }

    @Override
    public String getCategory() {
        return "Auto Pilot";
    }

    @Override
    public String getScriptCommandName() {
        return "symbex-only";
    }

    @Override
    public String getDescription() {
        return "Continue symbolic execution until no more modality is on the sequent.";
    }

    @Override
    protected Strategy<@NonNull Goal> createStrategy(Proof proof,
            PosInOccurrence posInOcc) {
        return new FilterSymbexStrategy(proof.getActiveStrategy());
    }

    public static boolean isAdmittedRule(RuleApp ruleApp) {
        Rule rule = ruleApp.rule();
        String name = rule.name().toString();
        if (ADMITTED_RULES.contains(name)) {
            return true;
        }

        if (rule instanceof org.key_project.prover.rules.Taclet taclet) {
            for (RuleSet rs : taclet.getRuleSets()) {
                if (ADMITTED_RULE_SETS.contains(rs.name().toString())) {
                    return true;
                }
            }
        }

        if("ifthenelse_split_for".equals(name)) {
            Term iteTerm = ruleApp.posInOccurrence().subTerm();
            Term then = iteTerm.sub(1);
            Term elze = iteTerm.sub(2);
            if(isUpdatedModality(then) && isUpdatedModality(elze)) {
                return true;
            }
        }

        // apply OSS to <inv>() calls.
        if (rule instanceof OneStepSimplifier) {
            PosInOccurrence pio = ruleApp.posInOccurrence();
            var target = pio.subTerm();
            if (isUpdatedModality(target)) {
                return true;
            }
        }

        if(rule instanceof UseOperationContractRule ||
                rule instanceof JmlAssertRule ||
                rule instanceof WhileInvariantRule ||
                rule instanceof LoopScopeInvariantRule )
            return true;

        return false;
    }

    private static boolean isUpdatedModality(Term term) {
        while(term.op() instanceof UpdateApplication) {
            term = term.sub(1);
        }
        return term.op() instanceof Modality;
    }

    private static class FilterSymbexStrategy extends FilterStrategy {

        private static final Name NAME = new Name(FilterSymbexStrategy.class.getSimpleName());
        private final Map<Sequent, Boolean> modalityCache = new WeakHashMap<>();

        public FilterSymbexStrategy(Strategy<@NonNull Goal> delegate) {
            super(delegate);
        }

        @Override
        public Name name() {
            return NAME;
        }

        @Override
        public boolean isApprovedApp(RuleApp app, PosInOccurrence pio, Goal goal) {
            if(!hasModality(goal)) {
                return false;
            }
            return isAdmittedRule(app) && super.isApprovedApp(app, pio, goal);
        }

        private boolean hasModality(Goal goal) {
            return modalityCache.computeIfAbsent(goal.node().sequent(), this::hasModality);
        }

        private boolean hasModality(Sequent seq) {
            for (SequentFormula formula : seq.asList()) {
                if (hasModality(formula.formula())) {
                    return true;
                }
            }
            return false;
        }

        private boolean hasModality(Term term) {
            if(term.op() instanceof Modality) {
                return true;
            }
            return term.subs().stream().anyMatch(this::hasModality);
        }

        @Override
        public boolean isStopAtFirstNonCloseableGoal() {
            return false;
        }
    }

}
