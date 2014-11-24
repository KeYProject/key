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

package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.io.File;

import javax.swing.JFileChooser;
import javax.swing.JOptionPane;

import de.uka.ilkd.key.gui.configuration.ProofIndependentSettings;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.util.Pair;

public class KeYFileChooser {

    private final JFileChooser fileChooser;

    private boolean saveDialog;

    private File resetFile = null;

    public KeYFileChooser(String initDir) {
	fileChooser = new JFileChooser(new File(initDir)) {
                /**
         * 
         */
        private static final long serialVersionUID = -7598570660247063980L;

                public void approveSelection() {
                    File file = getSelectedFile();
                    if (saveDialog && file.exists() &&
                            showOverwriteDialog(file) != JOptionPane.YES_OPTION) {
                        return;
                    }
                    super.approveSelection();
                }
            };
	fileChooser.setFileFilter(new javax.swing.filechooser.FileFilter() {
		public boolean accept(File f) {
		    return 
			    f.isDirectory()
			|| f.toString().endsWith(".java")
			|| f.toString().endsWith(".key") 
			|| f.toString().endsWith(".proof");
		}
		
		public String getDescription() {
		    return "Java files, KeY files and Source Directories";
		}
	    });
    }

    public void prepare() {
        File selFile = fileChooser.getSelectedFile();
        if ((selFile != null) && selFile.isFile()) { // present & not dir.
            String filename = selFile.getAbsolutePath();    
	    if (!filename.endsWith(".proof")) 
                fileChooser.setSelectedFile(new File(filename+".proof")); 
        }
    }

    public void setDialogTitle(String title) {
	if (title != null) {
	    fileChooser.setDialogTitle (title);
	} else {
	    fileChooser.setDialogTitle ("Select file to load");
	}
    }

    private void setSaveDialog(boolean b) {
        saveDialog = b;
	fileChooser.setFileSelectionMode(b 
		                         ? JFileChooser.FILES_ONLY 
		                         : JFileChooser.FILES_AND_DIRECTORIES);        
    }

    public Pair<Boolean, File> showSaveDialog(Component parent, String defaultName) {
        File file = fileChooser.getSelectedFile();
        final String recDir = file != null ?
                file.getParent() : fileChooser.getCurrentDirectory().toString();
        resetFile = (defaultName != null) ? new File(recDir, defaultName): file;
        fileChooser.setSelectedFile(resetFile);
        setSaveDialog(true);
        boolean proofFolderActive = ProofIndependentSettings.DEFAULT_INSTANCE
                         .getGeneralSettings().storesInDefaultProofFolder();
        final String poDir =
                resetFile.getParent().endsWith("src") ?
                        new File(resetFile.getParent()).getParent() : resetFile.getParent();
        final String proofFolder = ProofSaver.PROOF_SUBDIRECTORY;
        final String proofDir =
                (!proofFolderActive || resetFile.getParent().endsWith(proofFolder)) ?
                resetFile.getParent() : resetFile.getParent().concat(proofFolder);
        File dir = new File(proofDir);
        if (proofFolderActive && !dir.exists()) {
            dir.mkdir();
        } else {
            dir = null;
        }
        file = new File(defaultName.endsWith(".key") ? poDir : proofDir, resetFile.getName());
        final boolean res = showSaveDialog(parent, file);

	return new Pair<Boolean, File> (res, dir);
    }

    public void resetPath() {
        assert resetFile != null;
        fileChooser.setSelectedFile(resetFile);
        fileChooser.updateUI();
        resetFile = null;
    }

    public File getCurrentDirectory() {
       return fileChooser.getCurrentDirectory();
    }

   public boolean showSaveDialog(Component parent, File selectedFile) {
      if (selectedFile != null) {
         fileChooser.setSelectedFile(selectedFile);
         fileChooser.updateUI(); // Might prevent empty filename suggestion?
      }

      setSaveDialog(true);
      final boolean autoSave = MainWindow.getInstance().getUserInterface().autoSave();
      int result = autoSave ? JFileChooser.APPROVE_OPTION : fileChooser.showSaveDialog(parent);
      return (result == JFileChooser.APPROVE_OPTION);
   }

    public boolean showOpenDialog(Component component) {
        setSaveDialog(false);

        final File file = fileChooser.getSelectedFile() != null ?
                fileChooser.getSelectedFile() : fileChooser.getCurrentDirectory();
        resetFile = file;
        fileChooser.setSelectedFile(file);
        fileChooser.updateUI();

	int result = fileChooser.showOpenDialog(component);
	boolean res = (result == JFileChooser.APPROVE_OPTION);
	if (!res) {
	    this.resetPath();
	} else {
	    resetFile = null;
	}
	return res;
    }

    public File getSelectedFile() {
	return fileChooser.getSelectedFile();
    }

    public void selectFile(File f) {
	fileChooser.setSelectedFile(f);
    }

    private int showOverwriteDialog(File file) {
        return JOptionPane.showOptionDialog(fileChooser, "File " +
                file.getAbsolutePath() + " already exists. Overwrite?",
                "Save warning", JOptionPane.YES_NO_OPTION,
                JOptionPane.WARNING_MESSAGE, null, null, null);
    }
}