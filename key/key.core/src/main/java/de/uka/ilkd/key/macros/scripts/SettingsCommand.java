package de.uka.ilkd.key.macros.scripts;

import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.Varargs;

/**
 * This command is used to set variables in the proof environment.
 *
 * @author Alexander Weigl
 * @version 1 (11.05.17)
 */
public class SettingsCommand
        extends AbstractCommand<SettingsCommand.Parameters> {

    public static class Parameters {
        /** One Step Simplification parameter */
        @Option(value = "oss", required = false)
        public Boolean oneStepSimplification;
        /** Maximum number of proof steps parameter */
        @Option(value = "steps", required = false)
        public Integer proofSteps;
        /** Variable other parameters */
        @Varargs
        public Map<String, String> others = new LinkedHashMap<>();
    }

    public SettingsCommand() {
        super(Parameters.class);
    }

    @Override
    protected void execute(Parameters args)
            throws ScriptException, InterruptedException {
        if (args.oneStepSimplification != null) {
//            proof.getProofIndependentSettings().getGeneralSettings() FIXME: non-executable code
//                    .setOneStepSimplification(args.oneStepSimplification);

            log.info(String.format("Set oneStepSimplification to %s",
                    args.oneStepSimplification));
        }

        if (args.proofSteps != null) {
            proof.getSettings().getStrategySettings()
                    .setMaxSteps(args.proofSteps);
        }
    }

    @Override
    public String getName() {
        return "set";
    }
}
