/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.keyshortcuts;

import java.util.Map;
import java.util.Optional;
import java.util.TreeMap;

import javafx.scene.input.KeyCombination;

/**
 * Central registry of keyboard shortcuts of the JavaFX UI, counter-part of
 * {@code KeyStrokeManager}/{@code KeyStrokeSettings} of the Swing module {@code key.ui}.
 * <p>
 * Actions are keyed by the fully qualified class name of their Swing counterpart, so that the
 * persisted {@code keystrokes.json} of the Swing UI can be adopted by a later milestone. The
 * defaults mirror {@link javax.swing.KeyStroke KeyStrokeSettings}. Format parity (reading/writing
 * {@code keystrokes.json}) is deferred; the registry itself is the single source of truth for
 * accelerators.
 */
public final class KeyStrokeManagerF {

    private final Map<String, KeyCombination> bindings = new TreeMap<>();

    private KeyStrokeManagerF() {
        registerDefaults();
    }

    private static final KeyStrokeManagerF INSTANCE = new KeyStrokeManagerF();

    /**
     * @return the global shortcut manager instance
     */
    public static KeyStrokeManagerF getInstance() {
        return INSTANCE;
    }

    private static KeyCombination combo(String spec) {
        return KeyCombination.keyCombination(spec);
    }

    private void defineDefault(String actionId, String spec) {
        bindings.put(actionId, combo(spec));
    }

    /**
     * @return the registered shortcut for the given action, if any
     */
    public Optional<KeyCombination> binding(String actionId) {
        return Optional.ofNullable(bindings.get(actionId));
    }

    /**
     * Binds a shortcut to an action, overriding a possible default.
     *
     * @param actionId the action id
     * @param combination the shortcut, or {@code null} to remove the binding
     */
    public void bind(String actionId, KeyCombination combination) {
        if (combination == null) {
            bindings.remove(actionId);
        } else {
            bindings.put(actionId, combination);
        }
    }

    /**
     * Clears all overrides and re-establishes the default shortcuts.
     */
    public void resetToDefaults() {
        bindings.clear();
        registerDefaults();
    }

    /**
     * @return an immutable snapshot of the current bindings (action id → shortcut spec), ready for
     *         persistence
     */
    public Map<String, String> snapshot() {
        TreeMap<String, String> copy = new TreeMap<>();
        bindings.forEach((id, combo) -> copy.put(id, combo.getDisplayText()));
        return copy;
    }

    private void registerDefaults() {
        defineDefault("de.uka.ilkd.key.macros.FullAutoPilotProofMacro", modifier() + "V");
        defineDefault("de.uka.ilkd.key.macros.AutoPilotPrepareProofMacro", modifier() + "D");
        defineDefault("de.uka.ilkd.key.macros.PropositionalExpansionMacro", modifier() + "A");
        defineDefault("de.uka.ilkd.key.macros.FullPropositionalExpansionMacro", modifier() + "S");
        defineDefault("de.uka.ilkd.key.macros.TryCloseMacro", modifier() + "C");
        defineDefault("de.uka.ilkd.key.macros.FinishSymbolicExecutionMacro", modifier() + "X");
        defineDefault("de.uka.ilkd.key.macros.OneStepProofMacro", modifier() + "SPACE");
        defineDefault("de.uka.ilkd.key.macros.HeapSimplificationMacro", modifier() + "H");
        defineDefault("de.uka.ilkd.key.macros.UpdateSimplificationMacro", modifier() + "L");
        defineDefault("de.uka.ilkd.key.macros.IntegerSimplificationMacro", modifier() + "I");
        defineDefault("de.uka.ilkd.key.macros.SMTPreparationMacro", modifier() + "Y");

        defineDefault("de.uka.ilkd.key.gui.actions.SearchInProofTreeAction", modifier() + "F");
        defineDefault("de.uka.ilkd.key.gui.actions.PrettyPrintToggleAction", modifier() + "P");
        defineDefault("de.uka.ilkd.key.gui.actions.UnicodeToggleAction", modifier() + "U");
        defineDefault("de.uka.ilkd.key.gui.actions.ProofManagementAction", modifier() + "M");

        defineDefault("de.uka.ilkd.key.gui.actions.QuickSaveAction", "F5");
        defineDefault("de.uka.ilkd.key.gui.actions.QuickLoadAction", "F6");

        defineDefault("de.uka.ilkd.key.gui.actions.IncreaseFontSizeAction", modifier() + "PLUS");
        defineDefault("de.uka.ilkd.key.gui.actions.DecreaseFontSizeAction", modifier() + "MINUS");
        defineDefault("de.uka.ilkd.key.gui.actions.AbandonTaskAction", modifier() + "W");
        defineDefault("de.uka.ilkd.key.gui.actions.PruneProofAction", modifier() + "DELETE");
        defineDefault("de.uka.ilkd.key.gui.actions.GoalBackAction", modifier() + "Z");
        defineDefault("de.uka.ilkd.key.gui.actions.CopyToClipboardAction", modifier() + "C");
        defineDefault("de.uka.ilkd.key.gui.actions.ExitMainAction", modifier() + "Q");
        defineDefault("de.uka.ilkd.key.gui.actions.GoalSelectAboveAction", modifier() + "K");
        defineDefault("de.uka.ilkd.key.gui.actions.GoalSelectBelowAction", modifier() + "J");
        defineDefault("de.uka.ilkd.key.gui.actions.AutoModeAction", modifier() + "SPACE");
        defineDefault("de.uka.ilkd.key.gui.actions.OpenMostRecentFileAction", modifier() + "R");
        defineDefault("de.uka.ilkd.key.gui.actions.SaveBundleAction", modifier() + "B");
        defineDefault("de.uka.ilkd.key.gui.actions.SaveFileAction", modifier() + "S");
        defineDefault("de.uka.ilkd.key.gui.settings.SettingsManager$ShowSettingsAction",
            modifier() + "N");
        defineDefault("de.uka.ilkd.key.gui.actions.OpenFileAction", modifier() + "O");
        defineDefault("de.uka.ilkd.key.gui.actions.SearchInSequentAction", "F");
        defineDefault("de.uka.ilkd.key.gui.actions.SearchNextAction", "F3");
        defineDefault("de.uka.ilkd.key.gui.actions.SearchPreviousAction", "SHIFT+F3");
        defineDefault("de.uka.ilkd.key.gui.actions.SelectionBackAction", "SHORTCUT+ALT+LEFT");
        defineDefault("de.uka.ilkd.key.gui.actions.SelectionForwardAction", "SHORTCUT+ALT+RIGHT");
    }

    private static String modifier() {
        return "SHORTCUT+";
    }
}
