// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;
import java.io.File;

import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.IssueDialog;
import de.uka.ilkd.key.gui.KeYFileChooser;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofScriptWorker;
import de.uka.ilkd.key.proof.Proof;

/**
 * The Class ProofScriptFromFileAction.
 *
 * @author Mattias Ulbrich
 */
public class ProofScriptFromFileAction extends AbstractAction {
    private static final long serialVersionUID = -3181592516055470032L;

    private final KeYMediator mediator;

    private static File lastDirectory;

    /**
     * Instantiates a new proof script from file action.
     *
     * @param mediator the mediator
     */
    public ProofScriptFromFileAction(KeYMediator mediator) {
        super("Run proof script from file...");
        this.mediator = mediator;
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        File dir = null;
        if(lastDirectory != null) {
            dir = lastDirectory;
        } else {
            Proof currentProof = mediator.getSelectedProof();
            if(currentProof != null) {
                File currentFile = currentProof.getProofFile();
                if (currentFile != null) {
                    dir = currentFile.getParentFile();
                }
            } else {
                dir = new File(".");
            }
        }

        try {
            MainWindow mainWindow = MainWindow.getInstance();

            KeYFileChooser fc = KeYFileChooser.getFileChooser("Select file to load");
            fc.setFileFilter(fc.getAcceptAllFileFilter());
            fc.setCurrentDirectory(dir);
            int res = fc.showOpenDialog(mainWindow);
            if(res == JFileChooser.APPROVE_OPTION) {
                File selectedFile = fc.getSelectedFile();
                lastDirectory = selectedFile.getParentFile();
                ProofScriptWorker psw = new ProofScriptWorker(mediator, selectedFile);
                psw.init();
                psw.execute();
            }
        } catch (Exception ex) {
            IssueDialog.showExceptionDialog(MainWindow.getInstance(), ex);
        }
    }
}
