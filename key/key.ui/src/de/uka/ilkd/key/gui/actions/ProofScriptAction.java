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

import javax.swing.AbstractAction;
import javax.swing.JButton;
import javax.swing.JFileChooser;
import javax.swing.JPanel;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.ExceptionDialog;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.ProofScriptWorker;
import de.uka.ilkd.key.proof.Proof;

@SuppressWarnings("serial")
public class ProofScriptAction extends AbstractAction {

    private final KeYMediator mediator;

    private static File lastDirectory;

    public ProofScriptAction(KeYMediator mediator) {
        super("Run proof script ...");
        this.mediator = mediator;
    }

    @Override
    public void actionPerformed(ActionEvent e) {

        File dir;
        if(lastDirectory != null) {
            dir = lastDirectory;
        } else {
            Proof currentProof = mediator.getSelectedProof();
            if(currentProof != null) {
                dir = currentProof.getProofFile().getParentFile();
            } else {
                dir = new File(".");
            }
        }

        try {
            MainWindow mainWindow = MainWindow.getInstance();

            JFileChooser fc = new JFileChooser(dir);
            int res = fc.showOpenDialog(mainWindow);
            if(res == JFileChooser.APPROVE_OPTION) {
                File selectedFile = fc.getSelectedFile();
                lastDirectory = selectedFile.getParentFile();
                ProofScriptWorker psw = new ProofScriptWorker(mediator, selectedFile);
                psw.init();
                psw.execute();
            }
        } catch (Exception ex) {
            ExceptionDialog.showDialog(MainWindow.getInstance(), ex);
        }
    }

}
