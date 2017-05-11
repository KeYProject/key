package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletApp;

import java.util.Map;

/**
 * The assume command takes one argument:
 * * a formula to which the command is applied
 */
public class AssumeCommand
        extends AbstractCommand<AssumeCommand.FormulaParameter> {
    public AssumeCommand() {
        super(FormulaParameter.class);
    }

    public static class FormulaParameter {
        @Option("#2") public Term formula;
    }

    private static final Name TACLET_NAME = new Name("UNSOUND_ASSUME");

    @Override public FormulaParameter evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return ValueInjector.injection(new FormulaParameter(), arguments);
    }

    @Override public String getName() {
        return "assume";
    }

    @Override public void execute(FormulaParameter parameter)
            throws ScriptException, InterruptedException {
        Goal goal = state.getFirstOpenGoal();
        Taclet cut = proof.getEnv().getInitConfigForEnvironment()
                .lookupActiveTaclet(TACLET_NAME);
        TacletApp app = NoPosTacletApp.createNoPosTacletApp(cut);
        SchemaVariable sv = app.uninstantiatedVars().iterator().next();

        app = app.addCheckedInstantiation(sv, parameter.formula,
                proof.getServices(), true);
        goal.apply(app);
    }
}
