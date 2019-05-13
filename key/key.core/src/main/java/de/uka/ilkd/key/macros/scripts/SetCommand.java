package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.macros.scripts.meta.Option;

import java.util.Map;
import java.util.Properties;

public class SetCommand extends AbstractCommand<SetCommand.Parameters> {

    public SetCommand() {
        super(Parameters.class);
    }

    @Override public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override public void execute(Parameters args)
            throws ScriptException, InterruptedException {
        state.getProof().getSettings().update(args.getProperties());
    }

    @Override public String getName() {
        return "set";
    }

    static class Parameters {
        @Option("key")
        public String key;
        @Option("value")
        public String value;

        public Properties getProperties() {
            Properties p = new Properties();
            p.setProperty(key, value);
            return p;
        }
    }
}
