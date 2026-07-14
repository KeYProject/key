/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Action to show a dialog with the taclet options valid for the currently
 * selected proof.
 *
 * Now defers to the "Show Active Settings" action to show the taclet options.
 */
public class ShowActiveTactletOptionsAction extends MainWindowAction {

    private static final long serialVersionUID = -7012564698194718532L;
    private final ShowActiveSettingsAction action;

    public ShowActiveTactletOptionsAction(MainWindow mainWindow, ShowActiveSettingsAction action) {
        super(mainWindow);
        setName("Show Active Taclet Options");
        this.action = action;
    }

    @Override
    public void actionPerformed(ActionEvent e) {
        action.showAndFocusTacletOptions();
    }

    // @formatter:off

//    private void showActivatedChoices() {
//        Proof currentProof = proof == null ? getMediator().getSelectedProof() : proof;
//        if (currentProof == null) {
//            mainWindow.notify(new GeneralInformationEvent("No Options available.",
//                "If you wish to see Taclet Options " + "for a proof you have to load one first"));
//        } else {
//            StringBuilder message = new StringBuilder("Active Taclet Options:\n");
//            int rows = 0;
//            int columns = 0;
//            for (final String choice : currentProof.getSettings().getChoiceSettings()
//                    .getDefaultChoices().values()) {
//                message.append(choice).append("\n");
//                rows++;
//                if (columns < choice.length()) {
//                    columns = choice.length();
//                }
//            }
//            final JTextComponent activeOptions = new JTextArea(message.toString(), rows, columns);
//            activeOptions.setEditable(false);
//            Object[] toDisplay =
//                { activeOptions,
//                    "These options can be changed in Options->Show Settings->Taclet Options" };
//            JOptionPane.showMessageDialog(mainWindow, toDisplay,
//                "Taclet options used in the current proof", JOptionPane.INFORMATION_MESSAGE);
//        }
//    }
}
