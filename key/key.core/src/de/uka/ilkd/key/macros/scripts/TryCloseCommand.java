package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.macros.TryCloseMacro;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.ValueInjector;
import de.uka.ilkd.key.proof.Node;

import java.util.Map;

public class TryCloseCommand
        extends AbstractCommand<TryCloseCommand.TryCloseArguments> {
    public TryCloseCommand() {
        super(TryCloseArguments.class);
    }

    @Override public TryCloseArguments evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return ValueInjector.injection(this, new TryCloseArguments(), arguments);
    }

    @Override public void execute(TryCloseArguments args)
            throws ScriptException, InterruptedException {

        TryCloseMacro macro = args.steps == null ?
                new TryCloseMacro() :
                new TryCloseMacro(args.steps);

        boolean branch = "branch".equals(args.branch);
        Node target;
        if (branch) {
            target = state.getFirstOpenGoal().node();
        }
        else {
            target = state.getProof().root();
        }

        try {
            macro.applyTo(uiControl, target, null, uiControl);
        }
        catch (Exception e) {
            throw new ScriptException(
                    "tryclose caused an exception: " + e.getMessage(), e);
        }

    }

    @Override public String getName() {
        return "tryclose";
    }

    public static class TryCloseArguments {
        @Option(value = "steps", required = false)
        public Integer steps;
        @Option(value = "#2", required = false)
        public String branch;
    }
}
