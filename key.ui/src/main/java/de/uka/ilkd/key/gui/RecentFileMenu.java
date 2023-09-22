/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.event.ActionListener;
import java.io.*;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Properties;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.settings.PathConfig;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class offers a mechanism to manage recent files; it adds the necessary menu items to a menu
 * or even can provide that menu itself. also it offers a way to read the recent files from a
 * java.util.Properties object and can store them again to a Properties object. This class is a
 * result of the fusion of the RecentFileBuffer and RecentFiles classes. It's not a Menu in
 * itself!!!
 *
 * @author Ute Platzer, with a lot of input from Volker Braun.
 */
public class RecentFileMenu {
    private static final Logger LOGGER = LoggerFactory.getLogger(RecentFileMenu.class);

    /**
     * The maximum number of recent files displayed.
     */
    private static final int MAX_RECENT_FILES = 8;

    /**
     * this is the maximal number of recent files.
     */
    private int maxNumberOfEntries;

    /**
     * the menu
     */
    private final JMenu menu;

    /**
     * the actionListener to be notified of mouse-clicks or other actionevents on the menu items
     */
    private final ActionListener lissy;

    /**
     * recent files, unique by path
     */
    private final HashMap<String, RecentFileEntry> pathToRecentFile = new HashMap<>();
    /**
     * Mapping from menu item to entry
     */
    private final HashMap<JMenuItem, RecentFileEntry> menuItemToRecentFile;

    private RecentFileEntry mostRecentFile;

    /**
     * Create a new RecentFiles list.
     *
     * @param mediator Key mediator
     */
    public RecentFileMenu(final KeYMediator mediator) {
        this.menu = new JMenu("Recent Files");
        this.lissy = e -> {
            String absPath = getAbsolutePath((JMenuItem) e.getSource());
            File file = new File(absPath);

            // special case proof bundles -> allow to select the proof to load
            if (ProofSelectionDialog.isProofBundle(file.toPath())) {
                Path proofPath = ProofSelectionDialog.chooseProofToLoad(file.toPath());
                if (proofPath == null) {
                    // canceled by user!
                } else {
                    mediator.getUI().loadProofFromBundle(file, proofPath.toFile());
                }
            } else {
                mediator.getUI().loadProblem(file);
            }
        };
        this.maxNumberOfEntries = MAX_RECENT_FILES;

        this.menuItemToRecentFile = new LinkedHashMap<>();

        menu.setEnabled(menu.getItemCount() != 0);
        menu.setIcon(IconFactory.recentFiles(16));

        loadFrom(PathConfig.getRecentFileStorage());
    }

    private void insertFirstEntry(RecentFileEntry entry) {
        menu.insert(entry.getMenuItem(), 0);
        mostRecentFile = entry;
    }

    /**
     * add path to the menu
     */
    private void addNewToModelAndView(final String path) {
        // do not add quick save location to recent files
        if (de.uka.ilkd.key.gui.actions.QuickSaveAction.QUICK_SAVE_PATH.endsWith(path)) {
            return;
        }

        if (new File(path).exists()) {
            final RecentFileEntry entry = new RecentFileEntry(path);
            pathToRecentFile.put(entry.getAbsolutePath(), entry);

            // Recalculate unique names
            final String[] paths = pathToRecentFile.keySet().toArray(String[]::new);
            final ShortUniqueFileNames.Name[] names = ShortUniqueFileNames.makeUniqueNames(paths);
            // Set the names
            for (ShortUniqueFileNames.Name name : names) {
                pathToRecentFile.get(name.getPath()).setName(name.getName());
            }

            // Insert the menu item
            final JMenuItem item = entry.getMenuItem();
            menuItemToRecentFile.put(item, entry);
            item.addActionListener(lissy);

            insertFirstEntry(entry);
        }
    }

    /**
     *
     */
    private String getAbsolutePath(JMenuItem item) {
        return menuItemToRecentFile.get(item).getAbsolutePath();
    }

    private void addRecentFileNoSave(final String path) {
        LOGGER.trace("Adding file: {}", path);
        final RecentFileEntry existingEntry = pathToRecentFile.get(path);

        // Add the path to the recentFileList:
        // check whether this path is already there
        if (existingEntry != null) {
            menu.remove(existingEntry.getMenuItem());
            insertFirstEntry(existingEntry);
            return;
        }

        // if appropriate, remove the last entry.
        if (menu.getItemCount() == maxNumberOfEntries) {
            final JMenuItem item = menu.getItem(menu.getItemCount() - 1);
            final RecentFileEntry entry = menuItemToRecentFile.get(item);
            menuItemToRecentFile.remove(entry.getMenuItem());
            pathToRecentFile.remove(entry.getAbsolutePath());
            menu.remove(entry.getMenuItem());
        }
        addNewToModelAndView(path);
        menu.setEnabled(menu.getItemCount() != 0);
    }

    /**
     * call this method to add a new file to the beginning of the RecentFiles list. If the path is
     * already part of the list, it will be moved to the first position. No more than a specified
     * maximum number of names will be allowed in the list, and additional names will be removed at
     * the end. (set the maximum number with the {@link #setMaxNumberOfEntries(int i)} method).
     *
     * @param path the path of the file.
     */
    public void addRecentFile(final String path) {
        addRecentFileNoSave(path);
        save();
    }

    /**
     * specify the maximal number of recent files in the list. The default is MAX_RECENT_FILES
     */
    public void setMaxNumberOfEntries(int max) {
        if (maxNumberOfEntries > max && menu.getItemCount() > max) {
            for (int i = menu.getItemCount() - 1; i > max; i--) {
                menu.remove(i);
            }

        }
        this.maxNumberOfEntries = max;
    }

    /**
     * the menu where the recent files are kept. If the user didn't specify one in the constructor,
     * a new JMenu is created. It can be accessed via this method.
     */
    public JMenu getMenu() {
        return menu;
    }

    /**
     * read the recent file names from the properties object. the property names are expected to be
     * "RecentFile0" "RecentFile1" ...
     */
    private void load(Properties p) {
        int i = maxNumberOfEntries;
        do {
            String s = p.getProperty("RecentFile" + i);
            if (s != null) {
                addRecentFileNoSave(s);
            }
            i--;
        } while (i >= 0);
    }

    /**
     * Put the names of the recent Files into the properties object. The property names are
     * "RecentFile0" "RecentFile1" ... The values are fully qualified path names.
     */
    public void store(Properties p) {
        // if there's nothing to store:
        for (int i = 0; i < menu.getItemCount(); i++) {
            p.setProperty("RecentFile" + i, getAbsolutePath(menu.getItem(i)));
        }
    }

    /**
     * read the recent files from the given properties file
     */
    public final void loadFrom(String filename) {
        try (FileInputStream propStream = new FileInputStream(filename)) {
            Properties p = new Properties();
            p.load(propStream);
            load(p);
        } catch (FileNotFoundException ex) {
            LOGGER.debug("Could not read RecentFileList. Did not find file {}", filename);
        } catch (IOException ioe) {
            LOGGER.debug("Could not read RecentFileList. Some IO Error occured ", ioe);
        }
    }

    /**
     * @return the absolute path to the most recently opened file (maybe null)
     */
    public String getMostRecent() {
        return mostRecentFile != null ? mostRecentFile.getAbsolutePath() : null;
    }

    /**
     * write the recent file names to the given properties file. the file will be read (if it
     * exists) and then re-written so no information will be lost.
     */
    public void store(String filename) {
        File localRecentFiles = new File(filename);
        localRecentFiles.getParentFile().mkdirs();

        // creates a new file if it does not exist yet
        try {
            localRecentFiles.createNewFile();
        } catch (IOException e) {
            LOGGER.info("Could not create or access recent files", e);
            return;
        }

        Properties p = new Properties();
        try (FileInputStream fin = new FileInputStream(localRecentFiles);
                FileOutputStream fout = new FileOutputStream(localRecentFiles)) {
            p.load(fin);
            store(p);
            p.store(fout, "recent files");
        } catch (IOException ex) {
            LOGGER.info("Could not write recent files list ", ex);
        }
    }

    public void save() {
        store(PathConfig.getRecentFileStorage());
    }

    private static class RecentFileEntry {
        /**
         * full path
         */
        private final String absolutePath;
        /**
         * the associated menu item
         */
        private final JMenuItem menuItem;

        public RecentFileEntry(String absolutePath) {
            this.menuItem = new JMenuItem();
            this.menuItem.setToolTipText(absolutePath);
            this.absolutePath = absolutePath;
        }

        public String getAbsolutePath() {
            return absolutePath;
        }

        public void setName(String name) {
            this.menuItem.setText(name);
        }

        public JMenuItem getMenuItem() {
            return menuItem;
        }

        @Override
        public String toString() {
            return absolutePath;
        }
    }
}
