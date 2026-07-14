/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros;

import java.io.IOException;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.UpdateApplication;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.rule.*;
import de.uka.ilkd.key.strategy.Strategy;

import org.key_project.logic.Name;
import org.key_project.logic.Term;
import org.key_project.logic.op.Modality;
import org.key_project.prover.rules.Rule;
import org.key_project.prover.rules.RuleApp;
import org.key_project.prover.rules.RuleSet;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.Sequent;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.Streams;

import org.jspecify.annotations.NonNull;

/**
 * A proof macro that performs symbolic execution only, without applying any reasoning rules.
 *
 * <p>
 * This macro restricts rule application to a carefully selected set of rules that are safe
 * for symbolic execution. It continues executing until all modalities (program operators)
 * have been eliminated from the sequent, leaving only first-order proof obligations.
 * </p>
 * <p>
 * The admitted rules are loaded from resource files:
 * </p>
 * <ul>
 * <li>{@code SymbolicExecutionOnlyMacro.admittedRules.txt} - specific rule names</li>
 * <li>{@code SymbolicExecutionOnlyMacro.admittedRuleSets.txt} - entire rule sets</li>
 * </ul>
 * <p>
 * In addition to the configured rules, the following are always admitted:
 * </p>
 * <ul>
 * <li>{@code ifthenelse_split_for} when both branches contain updated modalities (Spec.
 * treatment)</li>
 * <li>{@link OneStepSimplifier} applications on updated modalities (for {@code <inv>()} calls)</li>
 * <li>{@link UseOperationContractRule}, {@link JmlAssertRule}, {@link WhileInvariantRule},
 * and {@link LoopScopeInvariantRule}</li>
 * </ul>
 * <p>
 * The macro uses a {@link FilterSymbexStrategy} that filters rule applications based on
 * {@link #isAdmittedRule(RuleApp)}. It also includes special handling to avoid infinite
 * recursion on the "throw null" branch of try-catch-throw constructs.
 * </p>
 * <p>
 * Accessible via the script command {@code "symbex-only"} and categorized under "Auto Pilot".
 * </p>
 *
 * <p>
 * Special treatment is required for throw clauses in case they are produced by treatment
 * of a throw clause. Then symb. execution might loop forever if not checked.
 * </p>
 *
 * @author mattias ulbrich
 * @see StrategyProofMacro
 * @see FilterSymbexStrategy
 */

public class SymbolicExecutionOnlyMacro extends StrategyProofMacro {

    private static final List<String> ADMITTED_RULES;
    private static final List<String> ADMITTED_RULE_SETS;
    static {
        try {
            ADMITTED_RULES = readLines("SymbolicExecutionOnlyMacro.admittedRules.txt");
            ADMITTED_RULE_SETS = readLines("SymbolicExecutionOnlyMacro.admittedRuleSets.txt");
        } catch (IOException e) {
            throw new RuntimeException(
                "Failed to load admitted rules for symbolic execution macro.", e);
        }
    }

    /**
     * Reads the (rule or rule set) names from a resource, one per line. Splits on any line
     * terminator and strips surrounding whitespace so that the entries also match when the
     * resource is checked out with CRLF line endings. Otherwise a trailing {@code '\r'} would
     * keep {@link #isAdmittedRule(RuleApp)} from ever matching, disabling symbolic execution on
     * Windows checkouts.
     */
    private static List<String> readLines(String resource) throws IOException {
        return Streams.toString(SymbolicExecutionOnlyMacro.class.getResourceAsStream(resource))
                .lines()
                .map(String::strip)
                .filter(s -> !s.isEmpty())
                .toList();
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

        if ("ifthenelse_split_for".equals(name)) {
            Term iteTerm = ruleApp.posInOccurrence().subTerm();
            Term then = iteTerm.sub(1);
            Term elze = iteTerm.sub(2);
            if (isUpdatedModality(then) && isUpdatedModality(elze)) {
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

        if (rule instanceof UseOperationContractRule ||
                rule instanceof JmlAssertRule ||
                rule instanceof WhileInvariantRule ||
                rule instanceof LoopScopeInvariantRule)
            return true;

        return false;
    }

    /**
     * return true if there is a boolean combination of updated modalities
     */
    private static boolean isUpdatedModality(Term term) {
        while (term.op() instanceof UpdateApplication) {
            term = term.sub(1);
        }
        if (term.op() instanceof Modality) {
            ;
            return true;
        }
        if (term.op() == Junctor.IMP || term.op() == Junctor.AND) {
            return term.subs().stream().allMatch(SymbolicExecutionOnlyMacro::isUpdatedModality);
        }
        return false;
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
            if (!hasModality(goal) || isThrowNullBranch(goal)) {
                return false;
            }
            return isAdmittedRule(app) && super.isApprovedApp(app, pio, goal);
        }

        /// Special case: Avoid infinite recursion on the "throw null" branch of tryCatchThrow
        /// by forbidding continuation on this branch.
        private boolean isThrowNullBranch(Goal goal) {
            return "Null reference in throw".equals(goal.node().getNodeInfo().getBranchLabel());
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
            if (term.op() instanceof Modality) {
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
