package de.uka.ilkd.key.macros.scripts;

import java.util.Map;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import static de.uka.ilkd.key.macros.scripts.EngineState.getGoal;

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
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    /**
     *
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
        Goal goal = state.getFirstOpenAutomaticGoal();
        Node node = goal.node();
        goal.apply(app);

        // TODO HACK! Renaming the goals to "show" and "use" to allow for references from scripts
        getGoal(goal.proof().openGoals(), node.child(0)).setBranchLabel("use");
        getGoal(goal.proof().openGoals(), node.child(1)).setBranchLabel("show");
    }

    public static class Parameters {
        @Option("#2")
        public Term formula;
    }

}
