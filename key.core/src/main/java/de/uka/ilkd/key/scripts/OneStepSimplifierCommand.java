/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.IBuiltInRuleApp;
import de.uka.ilkd.key.rule.OneStepSimplifierRuleApp;
import de.uka.ilkd.key.scripts.meta.Option;

import org.key_project.logic.PosInTerm;
import org.key_project.prover.sequent.PosInOccurrence;
import org.key_project.prover.sequent.SequentFormula;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

public class OneStepSimplifierCommand extends AbstractCommand {

    public OneStepSimplifierCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "oss";
    }

    @Override
    public void execute(ScriptCommandAst command) throws ScriptException, InterruptedException {

        var arguments = state().getValueInjector().inject(new Parameters(), command);

        final Goal goal = state.getFirstOpenAutomaticGoal();
        if (arguments.antecedent) {
            for (SequentFormula sf : goal.sequent().antecedent()) {
                ImmutableList<IBuiltInRuleApp> builtins = goal.ruleAppIndex().getBuiltInRules(goal,
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), true));
                for (IBuiltInRuleApp builtin : builtins) {
                    if (builtin instanceof OneStepSimplifierRuleApp) {
                        goal.apply(builtin);
                    }
                }
            }
        }

        if (arguments.succedent) {
            for (SequentFormula sf : goal.sequent().succedent()) {
                ImmutableList<IBuiltInRuleApp> builtins = goal.ruleAppIndex().getBuiltInRules(goal,
                    new PosInOccurrence(sf, PosInTerm.getTopLevel(), false));
                for (IBuiltInRuleApp builtin : builtins) {
                    if (builtin instanceof OneStepSimplifierRuleApp) {
                        goal.apply(builtin);
                    }
                }
            }
        }
    }

    public static class Parameters {
        @Option(value = "antecedent")
        public @Nullable Boolean antecedent = Boolean.TRUE;

        @Option(value = "succedent")
        public @Nullable Boolean succedent = Boolean.TRUE;
    }
}
