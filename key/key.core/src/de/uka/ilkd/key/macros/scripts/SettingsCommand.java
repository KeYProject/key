package de.uka.ilkd.key.macros.scripts;

import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.Varargs;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * This command is used to set variables in the proof environment.
 *
 * @author Alexander Weigl
 * @version 1 (11.05.17)
 */
public class SettingsCommand
        extends AbstractCommand<SettingsCommand.Parameters> {

    static class Parameters {
        @Option(value = "oss", required = false) Boolean oneStepSimplification;

        @Varargs Map<String, String> others = new LinkedHashMap<>();
    }

    public SettingsCommand() {
        super(Parameters.class);
    }

    @Override protected void execute(Parameters args)
            throws ScriptException, InterruptedException {
        if (args.oneStepSimplification != null) {
            proof.getProofIndependentSettings().getGeneralSettings()
                    .setOneStepSimplification(args.oneStepSimplification);

            log.info(String.format("Set oneStepSimplification to %s",
                    args.oneStepSimplification));
        }

    }

    @Override public String getName() {
        return "set";
    }
}
