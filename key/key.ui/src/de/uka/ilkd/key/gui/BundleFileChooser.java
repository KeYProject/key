package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.io.File;
import java.nio.file.FileSystems;
import java.nio.file.Path;
import java.nio.file.PathMatcher;

import javax.swing.JFileChooser;
import javax.swing.JOptionPane;
import javax.swing.filechooser.FileFilter;

import de.uka.ilkd.key.core.Main;

public class BundleFileChooser {
    // the desired extension for proof bundles can be configured here
    private static final String BUNDLE_EXT = "zproof";

    // TODO: abstract file chooser
    // TODO: path suggestions when started proof from java file
    // TODO: favorite directories
    // TODO: loading

    /* requirements:
     *  - favorite directories (see branch hackeyGUIkl)
     *  - path suggestion (should be in sync with KeYFileChooser)
     *  - filter: only zproof
     *  - two modes: load and save
     *      - in saving mode, return directly with the selected file
     *      - in loading mode, provide the possibilities to select the proofs to reload/replay
     */
    private static final FileFilter PROOF_PACKAGE_FILTER = new FileFilter() {
        public boolean accept(File f) {
            return f.getName().endsWith("." + BUNDLE_EXT) || f.isDirectory();
        }

        public String getDescription() {
            return "KeY proof packages (." + BUNDLE_EXT + ")";
        }
    };
    
    private static BundleFileChooser INSTANCE;

    private final JFileChooser fileChooser;
    
    private boolean saveDialog;
    
    private BundleFileChooser(File initDir) {
        fileChooser = new JFileChooser(initDir) {
            private static final long serialVersionUID = -7598570660247063980L;

            @Override
            public void approveSelection() {
                File file = getSaveFile().toFile();
                if (saveDialog && file.exists() &&
                                showOverwriteDialog(file) != JOptionPane.YES_OPTION) {
                    return;
                }
                super.approveSelection();
            }
        };
        fileChooser.setFileFilter(PROOF_PACKAGE_FILTER);
    }

    public boolean showSaveDialog(Component parent, File fileSuggestion) {
        if (fileSuggestion != null) {
            if (fileSuggestion.isDirectory()) {
                fileChooser.setSelectedFile(null);
                fileChooser.setCurrentDirectory(fileSuggestion);
            } else {
                fileChooser.setSelectedFile(fileSuggestion);
                fileChooser.updateUI(); // Might prevent empty filename suggestion?
            }
        }
        
        setSaveDialog(true);
        int result = fileChooser.showSaveDialog(parent);
        return (result == JFileChooser.APPROVE_OPTION);
    }

    private void setSaveDialog(boolean b) {
        saveDialog = b;
        fileChooser.setFileSelectionMode(b
                ? JFileChooser.FILES_ONLY
                        : JFileChooser.FILES_AND_DIRECTORIES);
    }
    
    public Path getSaveFile() {
        Path file = fileChooser.getSelectedFile().toPath();
        Path abs = file.toAbsolutePath();

        // replace file extension with .zproof if necessary
        PathMatcher matcher = FileSystems.getDefault().getPathMatcher("glob:*." + BUNDLE_EXT);
        if (!matcher.matches(abs)) {
            Path parent = abs.getParent();
            String name = abs.getFileName().toString();

            // replace or append extension
            int extStart = name.lastIndexOf('.');
            if (extStart == -1) {               // no extension given -> append
                abs = parent.resolve(name + "." + BUNDLE_EXT);
            } else {                            // extension given -> replace
                String newName = name.substring(0, extStart) + "." + BUNDLE_EXT;
                abs = parent.resolve(newName);
            }
        }
        return abs;
    }
    
    private int showOverwriteDialog(File file) {
        return JOptionPane.showOptionDialog(fileChooser, "File " +
                        file.getAbsolutePath() + " already exists. Overwrite?",
                        "Save warning", JOptionPane.YES_NO_OPTION,
                        JOptionPane.WARNING_MESSAGE, null, null, null);
    }
    
    public static BundleFileChooser getFileChooser(String title) {
        if (INSTANCE == null) {
            File initDir = Main.getWorkingDir();
            INSTANCE = new BundleFileChooser(initDir);
        }

        INSTANCE.fileChooser.setDialogTitle(title);
        //INSTANCE.prepare();
        return INSTANCE;
    }
}
