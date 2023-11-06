/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

/**
 * The assume command takes one argument: * a formula to which the command is applied
 */
public class AssumeCommand extends AbstractCommand<AssumeCommand.FormulaParameter> {
    private static final Name TACLET_NAME = new Name("UNSOUND_ASSUME");

    public AssumeCommand() {
        super(FormulaParameter.class);
    }

    @Override
    public FormulaParameter evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new FormulaParameter(), arguments);
    }

    @Override
    public String getName() {
        return "assume";
    }

    @Override
    public void execute(FormulaParameter parameter) throws ScriptException, InterruptedException {
        Taclet cut =
            state.getProof().getEnv().getInitConfigForEnvironment().lookupActiveTaclet(TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, parameter.formula, state.getProof().getServices(),
            true);
        state.getFirstOpenAutomaticGoal().apply(app);
    }

    public static class FormulaParameter {
        @Option("#2")
        public Term formula;
    }
}
