package de.uka.ilkd.key.gui.actions;

import java.awt.event.ActionEvent;

import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.MainWindow;

public class LemmaGenerationBatchModeAction extends MainWindowAction{
        
        private static final String description = "In case that one wants to prove a huge set of taclets, " +
        		"it can be convenient and useful to do this automatically.\n" +
        		"The new lemma generation offers now the possibility to use the batch mode of the KeY system\n" +
        		"in order to generate and prove the proof obligations for the correctness of (non-axiomatic) taclets.\n\n" +
        	
        		"The basic command using the batch mode is:\n\n"+
        		"runProver auto justifyRules FILE1 ?axioms FILE2 ?signature FILE3\n\n"+
        		"FILE1: The file containing the taclets that should be proved sound.\n"+
        		"FILE2: The file containing the taclets that should be used as axioms when proving the taclets of FILE1\n" +
        		"being sound.\n"+
        		"FILE3: The file containing the signature that should be used for loading the taclets.\n" +
        		"If this option is not set, the signature declared in FILE1 is used.\n\n"+
                "In order to store the resulting proofs to files one can set the option \"?saveProofToFile true\".\n"+
                "The corresponding proofs are stored into the folder in which FILE1 is located. In case that one wants to\n" +
                "store the proofs into another folder, one can specify the path of the folder by\n" +
                "\"?pathOfResult PATH_OF_DEST_FOLDER\".";

        public LemmaGenerationBatchModeAction(MainWindow mainWindow) {
                super(mainWindow);
                putValue(NAME,"Taclets using the Batch Mode");
                putValue(SHORT_DESCRIPTION,"A short description for using the batch mode.");
        }

        private static final long serialVersionUID = 1L;

        @Override
        public void actionPerformed(ActionEvent arg0) {
           
                JOptionPane.showMessageDialog(mainWindow, description, "Using the Batch Mode for Proving Taclets",
                                JOptionPane.INFORMATION_MESSAGE);
        }

}
