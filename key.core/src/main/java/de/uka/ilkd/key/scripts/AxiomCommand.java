/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.scripts;


import java.util.Objects;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.proof.mgt.ProofEnvironment;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.meta.Argument;
import de.uka.ilkd.key.scripts.meta.Documentation;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;

/// Deprecated command for adding formulas as axioms to the proof.
/// This is an alias for the `assume` command and should not be used in new scripts.
///
/// @see AssumeCommand
/// @deprecated Use `assume` instead
@Deprecated(forRemoval = true)
@Documentation(category = "Control", value = """
        This command is deprecated and should not be used in new scripts.
        Use the equivalent `assume` command instead.

        The axiom command adds a formula to the current sequent without proof obligation,
        effectively assuming it to be true. This is unsound and should only be used for
        testing or debugging purposes.
        """)
public class AxiomCommand extends AssumeCommand {
    private static final Name TACLET_NAME = new Name("cut");

    @Override
    public String getName() {
        return "axiom";
    }

    @Override
    public void execute(ScriptCommandAst args) throws ScriptException, InterruptedException {
        var parameter = state().getValueInjector().inject(new FormulaParameter(), args);

        ProofEnvironment env = Objects.requireNonNull(state().getProof().getEnv(),
            "proof environment is null");
        Taclet cut = Objects.requireNonNull(
            env.getInitConfigForEnvironment().lookupActiveTaclet(TACLET_NAME),
            "taclet 'cut' not found");
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv,
            Objects.requireNonNull(parameter.formula, "formula must be given"),
            state().getProof().getServices(), true);
        state().getFirstOpenAutomaticGoal()
                .apply(Objects.requireNonNull(app, "taclet application is null"));
    }

    public static class FormulaParameter {
        @Argument
        public @MonotonicNonNull JTerm formula;
    }
}
