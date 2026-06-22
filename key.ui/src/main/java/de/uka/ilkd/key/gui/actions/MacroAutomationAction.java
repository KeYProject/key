/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import javax.swing.Icon;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.macros.ProofMacro;

/**
 * Automation action that executes a proof macro.
 * <p>
 * This is a reusable wrapper for macro-based automation actions. Instead of creating separate
 * action classes for each macro, this generic wrapper can be used to expose any {@link ProofMacro}
 * as an automation option in the dropdown menu.
 * </p>
 *
 * @see ProofMacro
 */
public class MacroAutomationAction extends AutoModeAction {

    private static final long serialVersionUID = 1L;

    /** The proof macro to execute when this action is triggered. */
    private final ProofMacro macro;

    /**
     * Creates a new macro automation action.
     *
     * @param mainWindow the main window this action belongs to
     * @param macro the proof macro to execute
     * @param icon the icon displayed on the action button
     */
    public MacroAutomationAction(MainWindow mainWindow, ProofMacro macro, Icon icon) {
        super(mainWindow, icon);
        this.macro = macro;
        setName(macro.getName());
        setTooltip(macro.getDescription());
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        KeYMediator mediator = getMediator();
        if (mediator.isInAutoMode()) {
            getMediator().getUI().getProofControl().stopAutoMode();
        } else {
            mediator.getUI().getProofControl().runMacro(mediator.getSelectedNode(), macro, null);
        }
    }

    @Override
    public String toString() {
        return (String) getValue(NAME);
    }
}
