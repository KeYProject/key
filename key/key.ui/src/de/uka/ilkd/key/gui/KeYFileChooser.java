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
import javax.swing.filechooser.FileFilter;

import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.core.Main;


public class KeYFileChooser {
    
    private static final File HOME_DIR = IOUtil.getHomeDirectory();
    private static final FileFilter FILTER = new FileFilter() {
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
    };
    private static KeYFileChooser INSTANCE;

    private final JFileChooser fileChooser;
    


    private boolean saveDialog;

    private File resetFile = null;

    private KeYFileChooser(File initDir) {
        fileChooser = new JFileChooser(initDir) {
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
        fileChooser.setFileFilter(FILTER);
    }

    public void prepare() {
        File selFile = fileChooser.getSelectedFile();
        if ((selFile != null) && selFile.isFile()) { // present & not dir.
            String filename = selFile.getAbsolutePath();    
            if (!filename.endsWith(".proof")) 
                fileChooser.setSelectedFile(new File(filename+".proof")); 
        } else if (selFile == null) {
            fileChooser.setSelectedFile(null);
            fileChooser.setCurrentDirectory(HOME_DIR);
        } else { // is directory
            fileChooser.setSelectedFile(null);
            fileChooser.setCurrentDirectory(selFile);
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
    
    public boolean showSaveDialog(Component parent) {
        return showSaveDialog(parent, null, null);
    }

    /**
     * Show a file dialog for saving a file.
     * The dialog will provide a naming suggestion.
     * @param parent the main window
     * @param originalFile the original file to be saved, if it exists and is a proof, this will be the suggestion
     * @param extension the desired file name extension (usually ".proof")
     * @return
     */
    public boolean showSaveDialog(Component parent, File originalFile, String extension) {
        final String recDir = originalFile != null ?
                        // if directory stay there, otherwise go to parent directory
                        (originalFile.isDirectory()? originalFile.toString(): originalFile.getParent()) 
                        : fileChooser.getCurrentDirectory().toString();
        resetFile = (extension != null) ? new File(recDir, extension): originalFile;
        fileChooser.setSelectedFile(resetFile);
        setSaveDialog(true);
        final String poDir = resetFile.getParent().endsWith("src") ?
                             new File(resetFile.getParent()).getParent() : resetFile.getParent();
        final String proofDir = resetFile.getParent();
        originalFile = new File(extension.endsWith(".key") ? poDir : proofDir, resetFile.getName());
        return showSaveDialog(parent, originalFile);
    }


    private boolean showSaveDialog(Component parent, File selectedFile) {
        if (selectedFile != null) {
            if (selectedFile.isDirectory()) {
                fileChooser.setSelectedFile(null);
                fileChooser.setCurrentDirectory(selectedFile);
            } else {
                fileChooser.setSelectedFile(selectedFile);
                fileChooser.updateUI(); // Might prevent empty filename suggestion?
            }
        }

        setSaveDialog(true);
        int result = fileChooser.showSaveDialog(parent);
        return (result == JFileChooser.APPROVE_OPTION);
    }

    public void resetPath() {
        assert resetFile != null;
        if (resetFile.isDirectory()) {
            fileChooser.setSelectedFile(null);
            fileChooser.setCurrentDirectory(resetFile);
        } else {
            fileChooser.setSelectedFile(resetFile);
        }
        fileChooser.updateUI();
        resetFile = null;
    }

    public File getCurrentDirectory() {
        return fileChooser.getCurrentDirectory();
    }
    
    public boolean showOpenDialog(Component component) {
        setSaveDialog(false);

        final File file = fileChooser.getSelectedFile() != null ?
                        fileChooser.getSelectedFile() : fileChooser.getCurrentDirectory();
                        resetFile = file;
                        if (file.isDirectory()) {
                            fileChooser.setSelectedFile(null);
                            fileChooser.setCurrentDirectory(file);
                        } else {
                            fileChooser.setSelectedFile(file);
                        }
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

    /**
     * Gets <b>the</b> file chooser for the prover.
     * 
     * The chooser is created lazily when first requested. It points to the
     * directory of the command line argument (if present), otherwise to the
     * user's home directory.
     * 
     * @param title
     *            the title of the key file chooser
     * 
     * @return the key file chooser
     */
    public static KeYFileChooser getFileChooser(String title) {
        if (INSTANCE == null) {
            File initDir = Main.getWorkingDir();
            INSTANCE = new KeYFileChooser(initDir);
        }
        
        INSTANCE.setDialogTitle(title);
        INSTANCE.prepare();
        return INSTANCE;
    }
}