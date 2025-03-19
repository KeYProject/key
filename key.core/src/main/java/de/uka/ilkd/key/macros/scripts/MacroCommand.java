/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.macros.scripts;

import java.util.HashMap;
import java.util.Map;
import java.util.ServiceLoader;

import de.uka.ilkd.key.control.AbstractUserInterfaceControl;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.macros.ProofMacroFinishedInfo;
import de.uka.ilkd.key.macros.scripts.meta.Option;
import de.uka.ilkd.key.macros.scripts.meta.Varargs;
import de.uka.ilkd.key.pp.LogicPrinter;
import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.prover.impl.DefaultTaskStartedInfo;

public class MacroCommand extends AbstractCommand<MacroCommand.Parameters> {
    private static final Map<String, ProofMacro> macroMap = loadMacroMap();

    public MacroCommand() {
        super(Parameters.class);
    }

    private static Map<String, ProofMacro> loadMacroMap() {
        ServiceLoader<ProofMacro> loader = ServiceLoader.load(ProofMacro.class);
        Map<String, ProofMacro> result = new HashMap<>();

        for (ProofMacro proofMacro : loader) {
            String commandName = proofMacro.getScriptCommandName();
            if (commandName != null) {
                result.put(commandName, proofMacro);
            }
        }

        return result;
    }

    @Override
    public Parameters evaluateArguments(EngineState state, Map<String, String> arguments)
            throws Exception {
        return state.getValueInjector().inject(this, new Parameters(), arguments);
    }

    @Override
    public String getName() {
        return "macro";
    }

    @Override
    public void execute(AbstractUserInterfaceControl uiControl, Parameters args, EngineState state)
            throws ScriptException, InterruptedException {
        final Services services = state.getProof().getServices();
        // look up macro name
        ProofMacro macro = macroMap.get(args.macroName);
        if (macro == null) {
            throw new ScriptException("Macro '" + args.macroName + "' not found");
        }

        macro.resetParams();

        if (args.instantiations != null) {
            for (final Map.Entry<String, String> macroParam : args.instantiations.entrySet()) {
                if (macro.hasParameter(macroParam.getKey())) {
                    try {
                        macro.setParameter(macroParam.getKey(), macroParam.getValue());
                    } catch (IllegalArgumentException e) {
                        throw new ScriptException(String.format(
                            "Wrong format for parameter %s of macro %s: %s.\nMessage: %s",
                            macroParam.getKey(), args.macroName, macroParam.getValue(),
                            e.getMessage()));
                    }
                } else {
                    throw new ScriptException(String.format("Unknown parameter %s for macro %s",
                        macroParam.getKey(), args.macroName));
                }
            }
        }

        Goal g = state.getFirstOpenAutomaticGoal();
        ProofMacroFinishedInfo info =
            ProofMacroFinishedInfo.getDefaultInfo(macro, state.getProof());
        try {
            uiControl.taskStarted(
                new DefaultTaskStartedInfo(TaskStartedInfo.TaskKind.Macro, macro.getName(), 0));
            final Sequent sequent = g.node().sequent();
            PosInOccurrence pio = null;

            if (args.occ > -1) {
                pio = new PosInOccurrence(sequent.getFormulabyNr(args.occ + 1),
                    PosInTerm.getTopLevel(), args.occ + 1 <= sequent.antecedent().size());
            }

            final String matchRegEx = args.matches;
            if (matchRegEx != null) {
                pio = extractMatchingPio(sequent, matchRegEx, services);
            }

            synchronized (macro) {
                info = macro.applyTo(uiControl, g.node(), pio, uiControl);
            }
        } catch (Exception e) {
            throw new ScriptException(
                "Macro '" + args.macroName + "' raised an exception: " + e.getMessage(), e);
        } finally {
            uiControl.taskFinished(info);
            macro.resetParams();
        }
    }

    /**
     * TODO
     *
     * @param sequent
     * @param matchRegEx
     * @param services
     * @return
     * @throws ScriptException
     */
    public static PosInOccurrence extractMatchingPio(final Sequent sequent, final String matchRegEx,
            final Services services) throws ScriptException {
        PosInOccurrence pio = null;
        boolean matched = false;

        for (int i = 1; i < sequent.size() + 1; i++) {
            final boolean matchesRegex = formatTermString(
                LogicPrinter.quickPrintTerm(sequent.getFormulabyNr(i).formula(), services))
                        .matches(".*" + matchRegEx + ".*");
            if (matchesRegex) {
                if (matched) {
                    throw new ScriptException("More than one occurrence of a matching term.");
                }
                matched = true;
                pio = new PosInOccurrence(sequent.getFormulabyNr(i), PosInTerm.getTopLevel(),
                    i <= sequent.antecedent().size());
            }
        }

        if (!matched) {
            throw new ScriptException(
                String.format("Did not find a formula matching regex %s", matchRegEx));
        }

        return pio;
    }

    /**
     * Removes spaces and line breaks from the string representation of a term.
     *
     * @param str The string to "clean up".
     * @return The original without spaces and line breaks.
     */
    private static String formatTermString(String str) {
        return str //
                .replace("\n", " ") //
                .replace(" +", " ");
    }

    public static class Parameters {
        /** Macro name parameter */
        @Option("#2")
        public String macroName;
        /** Run on formula number "occ" parameter */
        @Option(value = "occ", required = false)
        public Integer occ = -1;
        /** Run on formula matching the given regex */
        @Option(value = "matches", required = false)
        public String matches = null;
        /** Variable macro parameters */
        @Varargs(as = String.class, prefix = "arg_")
        public Map<String, String> instantiations = new HashMap<>();
    }

}
