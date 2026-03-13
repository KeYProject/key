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
 * The command object CutCommand has as scriptcommand name "cut" As parameters: a formula with the
 * id "#2"
 */
public class CutCommand extends AbstractCommand {
    private static final Name CUT_TACLET_NAME = new Name("cut");

    public CutCommand() {
        super(Parameters.class);
    }

    @Override
    public String getName() {
        return "cut";
    }

    @Override
    public String getDocumentation() {
        return """
                CutCommand has as script command name "cut"

                As parameters:
                * a formula with the id "#2""";
    }

    @Override
    public void execute(ScriptCommandAst arguments) throws ScriptException, InterruptedException {
        var args = state().getValueInjector().inject(new Parameters(), arguments);
        execute(state(), args);
    }

    static void execute(EngineState state, Parameters args) throws ScriptException {
        Taclet cut = state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(CUT_TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, args.formula,
            state.getProof().getServices(), true);
        state.getFirstOpenAutomaticGoal().apply(app);
    }

    public static class Parameters {
        @Argument
        public @MonotonicNonNull JTerm formula;
    }

}
