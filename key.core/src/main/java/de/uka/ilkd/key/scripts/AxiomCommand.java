/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;


import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.meta.Argument;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

/**
 * The axiom command takes one argument: a formula to which the command is applied.
 *
 * @see AssumeCommand The assume command is a synonym for the axiom command.
 *
 * @deprecated This command is deprecated and should not be used in new scripts. It is kept for
 *             compatibility reasons.
 *             Use the {@link AssumeCommand} "assume" instead.
 */
@Deprecated(forRemoval = true)
public class AxiomCommand extends AssumeCommand {
    private static final Name TACLET_NAME = new Name("cut");

    @Override
    public String getName() {
        return "axiom";
    }

    @Override
    public void execute(ScriptCommandAst args) throws ScriptException, InterruptedException {
        var parameter = state().getValueInjector().inject(new FormulaParameter(), args);

        Taclet cut = state().getProof().getEnv()
                .getInitConfigForEnvironment().lookupActiveTaclet(TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, parameter.formula, state().getProof().getServices(),
            true);
        state().getFirstOpenAutomaticGoal().apply(app);
    }

    public static class FormulaParameter {
        @Argument
        public @MonotonicNonNull JTerm formula;
    }
}
