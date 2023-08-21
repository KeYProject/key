/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui.actions;

import java.awt.*;
import java.awt.event.ActionEvent;
import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.core.KeYSelectionEvent;
import de.uka.ilkd.key.core.KeYSelectionListener;
import de.uka.ilkd.key.gui.MainWindow;
import de.uka.ilkd.key.gui.fonticons.IconFactory;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * Opens the last opened file in an editor (well, it tries)
 */
public final class EditMostRecentFileAction extends MainWindowAction
        implements KeYSelectionListener {

    private static final Logger LOGGER = LoggerFactory.getLogger(EditMostRecentFileAction.class);

    private static final long serialVersionUID = -6214327707255790570L;

    public EditMostRecentFileAction(MainWindow mainWindow) {
        super(mainWindow);

        setName("Edit Last Opened File");
        setIcon(IconFactory.editFile(MainWindow.TOOLBAR_ICON_SIZE));
        setTooltip("Open the last opened file with the default external editor");

        setEnabled(mainWindow.getRecentFiles() != null
                && mainWindow.getRecentFiles().getMostRecent() != null);
        Desktop desktop = Desktop.getDesktop();
        if (!desktop.isSupported(Desktop.Action.EDIT)
                && !desktop.isSupported(Desktop.Action.OPEN)) {
            setEnabled(false);
        } else {
            mainWindow.getMediator().addKeYSelectionListener(this);
        }
    }

    public void actionPerformed(ActionEvent e) {
        if (mainWindow.getRecentFiles() != null
                && mainWindow.getRecentFiles().getMostRecent() != null) {
            final String recentFile = mainWindow.getRecentFiles().getMostRecent();
            if (recentFile != null) {
                File f = new File(recentFile);
                try {
                    EditFileActionHandler.getInstance().workWithFile(f);
                } catch (Exception exc) {
                    LOGGER.error("Error opening file in external application: {}",
                        exc.getMessage());
                }
            }
        }
    }

    @Override
    public void selectedProofChanged(KeYSelectionEvent e) {
        setEnabled(true);
    }

    /**
     * <p>
     * The method {@link #workWithFile(File)} of the default instance {@link #getInstance()} is used
     * by {@link EditMostRecentFileAction} to edit the last opened file or to open the last used
     * directory.
     * </p>
     * <p>
     * The advantage of this class is, that it is possible to exchange the implementation. This is
     * for instance done in the Eclipse integration where files are opened inside Eclipse instead of
     * the system editors.
     * </p>
     *
     * @author Martin Hentschel
     */
    public static class EditFileActionHandler {
        /**
         * The default instance.
         */
        public static EditFileActionHandler instance = new EditFileActionHandler();

        /**
         * Opens the given file in the default editor or opens the given directory.
         *
         * @param file The file to edit or the folder to open.
         * @throws IOException Occurred Exception.
         */
        public void workWithFile(File file) throws IOException {
            // WP: see #854: this uses the file registered for "Edit" action in Windows,
            // which can not be set via GUI.
            // As far as I know, for Linux/Mac, supportsEdit() always returns false. TODO: check
            // Therefore, we just use the "Open" action now.
            //
            // if (Main.getKeyDesktop().supportsEdit() && file.isFile()) {
            // Main.getKeyDesktop().edit(file);
            // } else {
            Desktop.getDesktop().open(file);
            // }
        }

        /**
         * Returns the default instance.
         *
         * @return The default instance.
         */
        public static EditFileActionHandler getInstance() {
            return instance;
        }

        /**
         * Sets the default instance.
         *
         * @param instance The default instance to set.
         */
        public static void setInstance(EditFileActionHandler instance) {
            EditFileActionHandler.instance = instance;
        }
    }
}
