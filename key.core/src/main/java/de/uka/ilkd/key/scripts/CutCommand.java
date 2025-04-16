/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;
import de.uka.ilkd.key.scripts.meta.Option;

import org.key_project.logic.Name;

/**
 * The command object CutCommand has as scriptcommand name "cut" As parameters: a formula with the
 * id "#2"
 */
public class CutCommand extends AbstractCommand<CutCommand.Parameters> {
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
    public Parameters evaluateArguments(EngineState state, Map<String, Object> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    /**
     * @param uiControl
     * @param args
     * @param state
     * @throws ScriptException
     * @throws InterruptedException
     */
    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters args, EngineState state)
            throws ScriptException, InterruptedException {
        Taclet cut = state.getProof().getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(CUT_TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, args.formula, state.getProof().getServices(), true);
        state.getFirstOpenAutomaticGoal().apply(app);
    }

    public static class Parameters {
        @Option("#2")
        public Term formula;
    }

}
