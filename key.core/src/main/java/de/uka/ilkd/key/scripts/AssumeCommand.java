/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.meta.Argument;
import de.uka.ilkd.key.scripts.meta.Documentation;

import org.key_project.logic.Name;
import org.key_project.logic.op.sv.SchemaVariable;

import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.NullMarked;

/**
 * The assume statement for proof debugging purposes
 * <p>
 * See exported documentation at @{@link FormulaParameter} at the end of this file.
 */
@NullMarked
public class AssumeCommand extends AbstractCommand {
    private static final Name TACLET_NAME = new Name("UNSOUND_ASSUME");

    public AssumeCommand() {
        super(FormulaParameter.class);
    }

    @Override
    public String getName() {
        return "assume";
    }

    @Override
    public String getDocumentation() {
        return """
                The assume command is an unsound taclet rule and takes one argument:

                The command adds the formula passed as argument to the antecedent
                a formula #2 to which the command is applied""";
    }


    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var parameter = state().getValueInjector()
                .inject(new FormulaParameter(), arguments);
        Taclet cut =
            state.getProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, parameter.formula, state.getProof().getServices(),
            true);
        state.getFirstOpenAutomaticGoal().apply(app);
    }

    public static class FormulaParameter {
        @Argument
        @Documentation("The formula to be assumed.")
        public @MonotonicNonNull JTerm formula;
    }
}
