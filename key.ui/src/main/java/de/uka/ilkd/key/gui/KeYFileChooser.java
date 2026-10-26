/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui;

import java.awt.Component;
import java.awt.Container;
import java.io.File;
import java.nio.file.Path;
import java.util.Locale;
import java.util.Objects;
import javax.swing.*;
import javax.swing.filechooser.FileFilter;
import javax.swing.filechooser.FileNameExtensionFilter;

import de.uka.ilkd.key.core.Main;

import org.key_project.util.java.IOUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Extends the usual Swing file chooser by a bookmark panel and predefined filters. This class is a
 * singleton, the only instance is created lazily and can be obtained via
 * {@link #getFileChooser(String)}. This has the benefit of remembering the last visited directory
 * across different load/save actions of the user. To keep it simple, the choosable file filters
 * contain all file extensions that are relevant in KeY. The predefined constants can be used to set
 * the corresponding filter via {@link #setFileFilter(FileFilter)}. Usually it is a good idea to do
 * this right after calling {@link #getFileChooser(String)}.
 *
 * @author Wolfram Pfeifer: refactoring: extend JFileChooser instead of wrapping it (avoids the need
 *         for delegating many methods)
 */
@NullMarked
public final class KeYFileChooser extends JFileChooser {

    /** default file filter for loading files */
    public static final FileFilter DEFAULT_FILTER = new FileFilter() {
        // FileNameExtensionFilter is not sufficient, as it only checks the part after the last dot
        @Override
        public boolean accept(File f) {
            String s = f.toString().toLowerCase(Locale.ROOT);
            return f.isDirectory() || s.endsWith(".java") || s.endsWith(".key")
                    || s.endsWith(".proof") || s.endsWith(".proof.gz") || s.endsWith(".zproof");
        }

        @Override
        public String getDescription() {
            return "Java files, (compressed) KeY files, proof bundles, and source directories";
        }
    };

    /** file filter for *.key files */
    public static final FileFilter KEY_FILTER = new FileNameExtensionFilter("KeY files", "key");

    /** The Constant for the filter for statistics files. */
    public static final FileFilter STATISTICS_FILTER =
        new FileNameExtensionFilter("proof statistics files (.csv, .html)", "csv", "html");

    /** file filter for proof management reports (*.html) */
    public static final FileFilter PROOF_MANAGEMENT_REPORT_FILTER =
        new FileNameExtensionFilter("proof management reports (.html)", "html");

    /** The Constant for the filter for dot files. */
    public static final FileFilter DOT_FILTER = new FileNameExtensionFilter(
        "dot graphviz files (.dot)", "dot");

    /** filter for single java source files */
    public static final FileFilter JAVA_FILTER =
        new FileNameExtensionFilter("Java source files (.java)", "java");

    /** filter for compressed proof files */
    public static final FileFilter COMPRESSED_FILTER = new FileFilter() {
        // FileNameExtensionFilter is not sufficient, as it only checks the part after the last dot
        @Override
        public boolean accept(File f) {
            return f.isDirectory() || f.toString().toLowerCase(Locale.ROOT).endsWith(".proof.gz");
        }

        @Override
        public String getDescription() {
            return "compressed proof files (.proof.gz)";
        }
    };

    /** filter for interaction log files */
    public static final FileFilter INTERACTION_LOG_FILTER =
        new FileNameExtensionFilter("interaction logs (.xml)", "xml");

    /** filter for zip archives */
    public static final FileFilter ZIP_FILTER =
        new FileNameExtensionFilter("ZIP archives (.zip)", "zip");

    /** filter for proof bundles */
    public static final FileFilter PROOF_BUNDLE_FILTER =
        new FileNameExtensionFilter("proof bundles (.zproof)", "zproof");

    /** The Constant for the home directory; {@code null} if the home directory is not available. */
    private final static @Nullable File HOME_DIR = IOUtil.getHomeDirectory();

    private static @Nullable KeYFileChooser INSTANCE;

    /** indicates whether the dialog is used for saving or loading */
    private boolean saveDialog;

    /** this is used to reset the path if the user presses the cancel button */
    private @Nullable File resetFile = null;

    public KeYFileChooser(File initDir) {
        super(initDir);

        // for simplicity, we always show all filters
        addChoosableFileFilter(DEFAULT_FILTER);
        addChoosableFileFilter(STATISTICS_FILTER);
        addChoosableFileFilter(PROOF_MANAGEMENT_REPORT_FILTER);
        addChoosableFileFilter(JAVA_FILTER);
        addChoosableFileFilter(COMPRESSED_FILTER);
        addChoosableFileFilter(INTERACTION_LOG_FILTER);
        addChoosableFileFilter(ZIP_FILTER);
        addChoosableFileFilter(PROOF_BUNDLE_FILTER);
        setFileFilter(DEFAULT_FILTER);

        setAccessory(new Box(BoxLayout.Y_AXIS));
    }

    public KeYFileChooserLoadingOptions addLoadingOptions() {
        var p = new KeYFileChooserLoadingOptions(this);
        Container accessory = getAccessory();
        if (accessory == null) {
            // the accessory is created by the constructor of this chooser
            throw new NullPointerException("No accessory available.");
        }
        accessory.add(p, 0);
        return p;
    }

    public KeYFileChooserBookmarkPanel addBookmarkPanel() {
        var p = new KeYFileChooserBookmarkPanel(this);
        Container accessory = getAccessory();
        if (accessory == null) {
            // the accessory is created by the constructor of this chooser
            throw new NullPointerException("No accessory available.");
        }
        accessory.add(p);
        return p;
    }

    public boolean useCompression() {
        File selectedFile = getSelectedFile();
        if (selectedFile == null) {
            // the caller invokes this only after a file has been selected
            throw new NullPointerException("No file selected.");
        }
        return selectedFile.getName().endsWith(".proof.gz");
    }

    @Override
    public void approveSelection() {
        File file = getSelectedFile();
        if (file == null) {
            // a file chooser always has a selection when approving
            throw new NullPointerException("No file selected.");
        }
        if (saveDialog && file.exists() && showOverwriteDialog(file) != JOptionPane.YES_OPTION) {
            return;
        }
        super.approveSelection();
    }

    public void prepare() {
        File selFile = getSelectedFile();

        if (selFile == null) {
            if (getCurrentDirectory() == null) {
                File homeDir = HOME_DIR;
                if (homeDir == null) {
                    // the home directory property is always available in KeY's environment
                    throw new NullPointerException("No home directory available.");
                }
                setCurrentDirectory(homeDir);
            }
        } else if (selFile.isFile()) { // present & not dir.
            String filename = selFile.getAbsolutePath();
            if (!filename.endsWith(".proof")) {
                setSelectedFile(new File(filename + ".proof"));
            }
        } else if (selFile.isDirectory()) {
            setCurrentDirectory(selFile);
        }
    }

    @Override
    public void setDialogTitle(@Nullable String title) {
        super.setDialogTitle(Objects.requireNonNullElse(title, "Select file to load"));
    }

    private void setSaveDialog(boolean b) {
        saveDialog = b;
        setFileSelectionMode(b ? FILES_ONLY : FILES_AND_DIRECTORIES);
    }

    @Override
    public int showSaveDialog(@Nullable Component parent) {
        return showSaveDialog(parent, null, null);
    }

    /**
     * Show a file dialog for saving a file. The dialog will provide a naming suggestion.
     *
     * @param parent the main window
     * @param originalFile the original file to be saved, if it exists and is a proof, this will be
     *        the suggestion
     * @param extension the desired file name extension (usually ".proof")
     * @return either of {@link #APPROVE_OPTION}, {@link #CANCEL_OPTION}, or {@link #ERROR_OPTION}
     */
    public int showSaveDialog(@Nullable Component parent, @Nullable File originalFile,
            @Nullable String extension) {
        File selectedFile;
        if (originalFile == null) {
            selectedFile = getCurrentDirectory();
        } else {
            selectedFile = originalFile.getAbsoluteFile();
            if (selectedFile.isFile()
                    || (!selectedFile.exists() && selectedFile.getName().contains("."))) {
                selectedFile = selectedFile.getParentFile();
            }
        }

        if (extension != null) {
            // the idea is to find the right place where to put a key vs. proof file
            // we should actually have a project file containing that information in a more reliable
            // way
            File dirForExtension = selectedFile;
            if (extension.endsWith(".key")) {
                // serach for "src" folder;
                while (dirForExtension != null && !"src".equals(dirForExtension.getName())) {
                    dirForExtension = dirForExtension.getParentFile();
                }
            }
            // project structure for KeY would be the sane thing to do; avoid NPE at any cost

            if (dirForExtension != null && "src".equals(dirForExtension.getName())
                    && dirForExtension.getParentFile() != null) {
                resetFile = dirForExtension.getParentFile();
            } else {
                resetFile = selectedFile;
            }

            File target = resetFile;
            if (target == null) {
                // the dialog always provides a current directory or an original file
                throw new NullPointerException("No target directory available.");
            }
            selectedFile = new File(target, extension);
        } else {
            resetFile = selectedFile;
        }

        setSelectedFile(resetFile);
        setSaveDialog(true);

        return showSaveDialog(parent, selectedFile);
    }

    /**
     * Shows the dialog with the given file/directory as currently selected.
     *
     * @param parent the Component the dialog is over
     * @param selectedFile the file or directory that shall be currently selected
     * @return either of {@link #APPROVE_OPTION}, {@link #CANCEL_OPTION}, or {@link #ERROR_OPTION}
     */
    public int showSaveDialog(@Nullable Component parent, @Nullable File selectedFile) {
        if (selectedFile != null) {
            if (selectedFile.isDirectory()) {
                setSelectedFile(null);
                setCurrentDirectory(selectedFile);
            } else {
                setSelectedFile(selectedFile);
                updateUI(); // Might prevent empty filename suggestion?
            }
        }

        if (resetFile == null) {
            File currentDirectory = getCurrentDirectory();
            if (currentDirectory == null) {
                // the file chooser always provides a current directory
                throw new NullPointerException("No current directory available.");
            }
            resetFile = currentDirectory;
        }

        setSaveDialog(true);
        int result = super.showSaveDialog(parent);
        if (result != APPROVE_OPTION) {
            resetPath();
        }
        return result;
    }

    private void resetPath() {
        File currentReset = resetFile;
        if (currentReset == null) {
            // resetFile is always assigned before the dialog is shown
            throw new NullPointerException("No reset file available.");
        }
        if (currentReset.isDirectory()) {
            setSelectedFile(null);
            setCurrentDirectory(currentReset);
        } else {
            setSelectedFile(currentReset);
        }
        updateUI();
        resetFile = null;
    }

    @Override
    public int showOpenDialog(@Nullable Component component) {
        setSaveDialog(false);

        final File file = getSelectedFile() != null ? getSelectedFile() : getCurrentDirectory();
        if (file == null) {
            // the file chooser always provides a selection or a current directory
            throw new NullPointerException("No file available.");
        }
        resetFile = file;
        if (file.isDirectory()) {
            setSelectedFile(null);
            setCurrentDirectory(file);
        } else {
            setSelectedFile(file);
        }
        updateUI();

        int result = super.showOpenDialog(component);
        if (result != APPROVE_OPTION) {
            resetPath();
        } else {
            resetFile = null;
        }
        return result;
    }

    private int showOverwriteDialog(File file) {
        return JOptionPane.showOptionDialog(this,
            "File " + file.getAbsolutePath() + " already exists. Overwrite?", "Save warning",
            JOptionPane.YES_NO_OPTION, JOptionPane.WARNING_MESSAGE, null, new Object[0], null);
    }

    /**
     * Gets <b>the</b> file chooser for the prover.
     *
     * The chooser is created lazily when first requested. It points to the directory of the command
     * line argument (if present), otherwise to the user's home directory.
     *
     * @param title the title of the key file chooser
     *
     * @return the key file chooser
     */
    public static KeYFileChooser getFileChooser(String title) {
        if (INSTANCE == null) {
            Path workingDir = Main.getWorkingDir();
            if (workingDir == null) {
                // the command line always provides a working directory
                throw new NullPointerException("No working directory available.");
            }
            File initDir = workingDir.toFile();
            INSTANCE = new KeYFileChooser(initDir);

            // not the best design probably: this constructor has the side effect of connecting
            // the new bookmark panel to the file chooser.
            INSTANCE.addBookmarkPanel();
        }

        INSTANCE.setDialogTitle(title);
        INSTANCE.prepare();
        return INSTANCE;
    }
}
