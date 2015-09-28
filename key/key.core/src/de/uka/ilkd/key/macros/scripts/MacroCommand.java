package de.uka.ilkd.key.macros.scripts;

import java.util.HashMap;
import java.util.Map;
import java.util.ServiceLoader;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.proof.DefaultTaskStartedInfo;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.TaskStartedInfo;

public class MacroCommand extends AbstractCommand {

    private static Map<String, ProofMacro> macroMap = loadMacroMap();

    @Override
    public String getName() {
        return "macro";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Proof proof,
            Map<String, String> args, Map<String, Object> state) throws ScriptException, InterruptedException {

        String macroName = args.get("#2");

        //
        // look up macro name
        ProofMacro macro = macroMap.get(macroName);
        if(macro == null) {
            throw new ScriptException("Macro '" + macroName + "' not found");
        }

        Goal g = getFirstOpenGoal(proof, state);
        ProofMacroFinishedInfo info = ProofMacroFinishedInfo.getDefaultInfo(macro, proof);
        try {
            uiControl.taskStarted(new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Macro, macro.getName(), 0));
            synchronized (macro) {
                info = macro.applyTo(uiControl, g.node(), null, uiControl);
            }
        } catch (Exception e) {
            throw new ScriptException("Macro '" + macroName + "' raised an exception: " + e.getMessage(), e);
        } finally {
            uiControl.taskFinished(info);
        }

    }


    private static Map<String, ProofMacro> loadMacroMap() {
        ServiceLoader<ProofMacro> loader = ServiceLoader.load(ProofMacro.class);
        Map<String, ProofMacro> result = new HashMap<String, ProofMacro>();

        for (ProofMacro proofMacro : loader) {
            String commandName = proofMacro.getScriptCommandName();
            if(commandName != null) {
                result.put(commandName, proofMacro);
            }
        }

        return result;
    }

}
