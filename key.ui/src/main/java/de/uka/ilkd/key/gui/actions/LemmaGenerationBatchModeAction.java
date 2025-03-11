/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.MainWindow;

public class LemmaGenerationBatchModeAction extends MainWindowAction {

    private static final String DESCRIPTION =
        """
                In case that one wants to prove a huge set of taclets, it can be convenient and useful to do this automatically.
                The new lemma generation offers now the possibility to use the batch mode of the KeY system
                in order to generate and prove the proof obligations for the correctness of (non-axiomatic) taclets.

                The basic command using the batch mode is:

                runProver --justify-rules  FILE1 --jr-axioms FILE2 --jr-signature FILE3

                FILE1: The file containing the taclets that should be proved sound.
                FILE2: The file containing the taclets that should be used as axioms when proving the taclets of FILE1
                being sound.
                FILE3: The file containing the signature that should be used for loading the taclets.
                If this option is not set, the signature declared in FILE1 is used.

                In order to store the resulting proofs to files one can set the option "--jr-saveProofToFile true".
                The corresponding proofs are stored into the folder in which FILE1 is located. In case that one wants to
                store the proofs into another folder, one can specify the path of the folder by
                "--jr-pathOfResult PATH_OF_DEST_FOLDER".
                Some more options are available, which are shown when using the command:\s

                runProver --help
                in the batch mode.""";

    private static final long serialVersionUID = 1L;

    public LemmaGenerationBatchModeAction(MainWindow mainWindow) {
        super(mainWindow);
        setTooltip("Show information about proving taclets by using the batch mode.");
        putValue(NAME, "Taclets Using the Batch Mode...");
        putValue(SHORT_DESCRIPTION, "A short description for using the batch mode.");
    }

    @Override
    public void actionPerformed(ActionEvent arg0) {
        JOptionPane.showMessageDialog(mainWindow, DESCRIPTION,
            "Using the Batch Mode for Proving Taclets", JOptionPane.INFORMATION_MESSAGE);
    }
}
