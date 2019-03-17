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
                            || "java".equals(IOUtil.getFileExtension(f))
                            || "key".equals(IOUtil.getFileExtension(f))
                            || "proof".equals(IOUtil.getFileExtension(f))
                            || f.getName().endsWith(".proof.gz");
        }

        public String getDescription() {
            return "Java files, (compressed) KeY files and source directories";
        }
    };

    private static final FileFilter COMPRESSED_FILTER = new FileFilter() {
        public boolean accept(File f) {
            return f.getName().endsWith(".proof.gz") || f.isDirectory();
        }

        public String getDescription() {
            return "compressed KeY proof files (.proof.gz)";
        }
    };


    private static KeYFileChooser INSTANCE;

    private final JFileChooser fileChooser;

    private boolean saveDialog;

    private File resetFile = null;

    public boolean useCompression() {
        return getSelectedFile().getName().endsWith(".proof.gz");
    }

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
        fileChooser.addChoosableFileFilter(COMPRESSED_FILTER);
        fileChooser.setFileFilter(FILTER);
    }

    public void prepare() {
        File selFile = fileChooser.getSelectedFile();
        
        if (selFile == null) {
            if (fileChooser.getCurrentDirectory() == null) {
                fileChooser.setCurrentDirectory(HOME_DIR);                
            } 
        } else if (selFile.isFile()) { // present & not dir.
            String filename = selFile.getAbsolutePath();
            if (!filename.endsWith(".proof"))
                fileChooser.setSelectedFile(new File(filename+".proof"));
        } else if (selFile.isDirectory()) {
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
        File selectedFile;
        if (originalFile == null) {
            selectedFile = fileChooser.getCurrentDirectory();
        } else {
            selectedFile = originalFile.getAbsoluteFile();
            if (selectedFile.isFile() || (!selectedFile.exists() && selectedFile.getName().contains("."))) {
                selectedFile = selectedFile.getParentFile();
            }
        }
        
        if (extension != null) {
            // the idea is to find the right place where to put a key vs. proof file
            // we should actually have a project file containing that information in a more reliable way
            File dirForExtension = selectedFile;
            if (extension.endsWith(".key")) {
                // serach for "src" folder; 
                while (dirForExtension != null && !"src".equals(dirForExtension.getName())) {
                    dirForExtension = dirForExtension.getParentFile();                    
                }
            }
            // project structure for KeY would be the sane thing to do; avoid NPE at any cost
            
            resetFile = "src".equals(dirForExtension.getName()) && dirForExtension.getParentFile() != null ? 
                    dirForExtension.getParentFile() : selectedFile;
            
            selectedFile = new File(resetFile, extension);             
        } else {
            resetFile = selectedFile;
        }
        
        
        fileChooser.setSelectedFile(resetFile);
        setSaveDialog(true);
        
        return showSaveDialog(parent, selectedFile);
    }

    public boolean showSaveDialog(Component parent, File selectedFile) {
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