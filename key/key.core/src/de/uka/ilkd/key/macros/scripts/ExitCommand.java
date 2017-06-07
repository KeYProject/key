package de.uka.ilkd.key.macros.scripts;


import de.uka.ilkd.key.control.AbstractUserInterfaceControl;

public class ExitCommand extends NoArgumentCommand {
    @Override public void execute(AbstractUserInterfaceControl uiControl,
            Void args, EngineState stateMap)
            throws ScriptException, InterruptedException {
        throw new InterruptedException(
                "Interruption requested from within script");

    }

    @Override public String getName() {
        return "exit";
    }
}
