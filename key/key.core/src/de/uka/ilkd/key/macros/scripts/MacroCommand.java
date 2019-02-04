package de.uka.ilkd.key.macros.scripts;

import java.util.HashMap;
import java.util.Map;
import java.util.ServiceLoader;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.Varargs;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;

public class MacroCommand extends AbstractCommand<MacroCommand.Parameters> {
    private static Map<String, ProofMacro> macroMap = loadMacroMap();

    public MacroCommand() {
        super(Parameters.class);
    }

    private static Map<String, ProofMacro> loadMacroMap() {
        ServiceLoader<ProofMacro> loader = ServiceLoader.load(ProofMacro.class);
        Map<String, ProofMacro> result = new HashMap<String, ProofMacro>();

        for (ProofMacro proofMacro : loader) {
            String commandName = proofMacro.getScriptCommandName();
            if (commandName != null) {
                result.put(commandName, proofMacro);
            }
        }

        return result;
    }

    @Override
    public Parameters evaluateArguments(EngineState state,
            Map<String, String> arguments) throws Exception {
        return state.getValueInjector().inject(this, new Parameters(),
                arguments);
    }

    @Override
    public String getName() {
        return "macro";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters args,
            EngineState state) throws ScriptException, InterruptedException {
        // look up macro name
        ProofMacro macro = macroMap.get(args.macroName);
        if (macro == null) {
            throw new ScriptException(
                    "Macro '" + args.macroName + "' not found");
        }

        macro.resetParams();

        if (args.instantiations != null) {
            for (final Map.Entry<String, String> macroParam : args.instantiations
                    .entrySet()) {
                if (macro.hasParameter(macroParam.getKey())) {
                    try {
                        macro.setParameter(macroParam.getKey(),
                                macroParam.getValue());
                    }
                    catch (IllegalArgumentException e) {
                        throw new ScriptException(String.format(
                                "Wrong format for parameter %s of macro %s: %s.\nMessage: %s",
                                macroParam.getKey(), args.macroName,
                                macroParam.getValue(), e.getMessage()));
                    }
                }
                else {
                    throw new ScriptException(
                            String.format("Unknown parameter %s for macro %s",
                                    macroParam.getKey(), args.macroName));
                }
            }
        }

        Goal g = state.getFirstOpenGoal();
        ProofMacroFinishedInfo info = ProofMacroFinishedInfo
                .getDefaultInfo(macro, state.getProof());
        try {
            uiControl.taskStarted(new DefaultTaskStartedInfo(
                    TaskStartedInfo.TaskKind.Macro, macro.getName(), 0));
            PosInOccurrence pio = null;
            if (args.occ > -1) {
                pio = new PosInOccurrence(
                        g.node().sequent().getFormulabyNr(args.occ + 1),
                        PosInTerm.getTopLevel(),
                        args.occ + 1 <= g.node().sequent().antecedent().size());
            }

            synchronized (macro) {
                info = macro.applyTo(uiControl, g.node(), pio, uiControl);
            }

            state.setGoal((Goal) null);
        }
        catch (Exception e) {
            throw new ScriptException("Macro '" + args.macroName
                    + "' raised an exception: " + e.getMessage(), e);
        }
        finally {
            uiControl.taskFinished(info);
            macro.resetParams();
        }

    }

    public static class Parameters {
        @Option("#2")
        public String macroName;
        @Option(value = "occ", required = false)
        public Integer occ = -1;
        @Varargs(as = String.class, prefix = "arg_")
        public Map<String, String> instantiations = new HashMap<>();
    }

}
