/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import javax.swing.Icon;

import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.macros.ProofMacro;
import de.uka.ilkd.key.proof.Proof;

/**
 * Automation action that executes a proof macro.
 * <p>
 * This is a reusable wrapper for macro-based automation actions. Instead of creating separate
 * action classes for each macro, this generic wrapper can be used to expose any {@link ProofMacro}
 * as an automation option in the dropdown menu.
 * </p>
 * <p>
 * Example usage:
 *
 * <pre>
 * {@code
 * actions.add(new MacroAutomationAction(mainWindow,
 *     new FullAutoPilotProofMacro(),
 *     "Full Auto Pilot",
 *     IconFactory.automationFullPilotLogo(16)));
 * }
 * </pre>
 * </p>
 *
 * @see ProofMacro
 * @see MainWindow#createAutomationActions()
 */
public class MacroAutomationAction extends MainWindowAction {

    private static final long serialVersionUID = 1L;

    /** The proof macro to execute when this action is triggered. */
    private final ProofMacro macro;

    /**
     * Creates a new macro automation action.
     *
     * @param mainWindow the main window this action belongs to
     * @param macro the proof macro to execute
     * @param name the display name shown in the dropdown menu
     * @param icon the icon displayed on the action button
     */
    public MacroAutomationAction(MainWindow mainWindow, ProofMacro macro, String name, Icon icon) {
        super(mainWindow);
        this.macro = macro;
        putValue(NAME, name);
        putValue(SHORT_DESCRIPTION, macro.getDescription());
        putValue(SMALL_ICON, icon);
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        if (!getMediator().isInAutoMode()) {
            Proof proof = getMediator().getSelectedProof();
            if (proof != null && !proof.closed()) {
                getMediator().getUI().getProofControl()
                        .runMacro(getMediator().getSelectedNode(), macro, null);
            }
        }
    }

    @Override
    public String toString() {
        return (String) getValue(NAME);
    }
}
