/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.gui;

import java.awt.event.ActionEvent;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import javax.swing.*;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;

import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static de.uka.ilkd.key.gui.actions.QuickSaveAction.QUICK_SAVE_PATH;

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

    private final KeYMediator mediator;

    /**
     * this is the maximal number of recent files.
     */
    private int maxNumberOfEntries;

    /**
     * the menu
     */
    private final JMenu menu;

    /**
     * Mapping from menu item to entry
     */
    private final List<RecentFileEntry> recentFiles = new ArrayList<>();

    private RecentFileEntry mostRecentFile;

    /**
     * Create a new RecentFiles list.
     *
     * @param mediator Key mediator
     */
    public RecentFileMenu(final KeYMediator mediator) {
        this.mediator = mediator;
        this.menu = new JMenu("Recent Files");
        this.maxNumberOfEntries = MAX_RECENT_FILES;

        // menu.setEnabled(menu.getItemCount() != 0);
        menu.setIcon(IconFactory.recentFiles(16));

        loadFrom(PathConfig.getRecentFileStorage());
    }

    private void insertFirstEntry(RecentFileEntry entry) {
        menu.insert(entry.createMenuItem(), 0);
        mostRecentFile = entry;
    }

    /**
     * add path to the menu
     */
    private void addNewToModelAndView(final String path,
            @Nullable Profile profile,
            boolean singleJava, @Nullable Configuration additionalOption) {
        // do not add quick save location to recent files
        if (QUICK_SAVE_PATH.endsWith(path)) {
            return;
        }

        if (new File(path).exists()) {
            var entry = new RecentFileEntry(path, profile != null ? profile.displayName() : null,
                singleJava, additionalOption);

            // Recalculate unique names
            final String[] paths =
                recentFiles.stream().map(RecentFileEntry::getAbsolutePath).toArray(String[]::new);
            final ShortUniqueFileNames.Name[] names = ShortUniqueFileNames.makeUniqueNames(paths);

            // Set the names
            for (ShortUniqueFileNames.Name name : names) {
                // TODO pathToRecentFile.get(name.getPath()).setName(name.getName());
            }

            insertFirstEntry(entry);
        }
    }

    private void addRecentFileNoSave(final String path,
            @Nullable Profile profile,
            boolean singleJava,
            @Nullable Configuration additionalOption) {
        LOGGER.trace("Adding file: {}", path);

        Optional<RecentFileEntry> existingEntry = recentFiles.stream()
                .filter(it -> path.equals(it.getAbsolutePath())).findFirst();

        // Add the path to the recentFileList:
        // check whether this path is already there
        if (existingEntry.isPresent()) {
            var entry = existingEntry.get();
            recentFiles.remove(entry);
            menu.remove(entry.createMenuItem());
            insertFirstEntry(entry);
            return;
        }

        // if appropriate, remove the last entry.
        if (menu.getItemCount() == maxNumberOfEntries) {
            var lastEntry = recentFiles.removeLast();
            menu.remove(lastEntry.createMenuItem());
        }
        addNewToModelAndView(path, profile, singleJava, additionalOption);
        menu.setEnabled(menu.getItemCount() != 0);
    }

    /**
     * call this method to add a new file to the beginning of the RecentFiles list. If the path is
     * already part of the list, it will be moved to the first position. No more than a specified
     * maximum number of names will be allowed in the list, and additional names will be removed at
     * the end. (set the maximum number with the {@link #setMaxNumberOfEntries(int i)} method).
     *
     * @param path the path of the file.
     * @param singleJava
     */
    public void addRecentFile(final String path,
            @Nullable Profile profile, boolean singleJava,
            @Nullable Configuration additionalOption) {
        addRecentFileNoSave(path, profile, singleJava, additionalOption);
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
     * read the recent files from the given properties file
     */
    public final void loadFrom(Path filename) {
        try {
            var file = ParsingFacade.parseConfigurationFile(filename);
            List<Configuration> recent = file.asConfigurationList();
            this.recentFiles.clear();
            for (var c : recent) {
                final var e = new RecentFileEntry(c);
                if (mostRecentFile != null) {
                    mostRecentFile = e;
                }
                recentFiles.add(e);
                menu.add(e.createMenuItem());
            }
        } catch (FileNotFoundException ex) {
            LOGGER.debug("Could not read RecentFileList. Did not find file {}", filename);
        } catch (IOException ioe) {
            LOGGER.debug("Could not read RecentFileList. Some IO Error occured ", ioe);
        }
    }

    /**
     * @return the absolute path to the most recently opened file (maybe null)
     */
    @Nullable
    public String getMostRecent() {
        return mostRecentFile != null ? mostRecentFile.getAbsolutePath() : null;
    }

    /**
     * write the recent file names to the given properties file. the file will be read (if it
     * exists) and then re-written so no information will be lost.
     */
    public void store(Path filename) {
        List<Configuration> config =
            recentFiles.stream().map(RecentFileEntry::asConfiguration).toList();
        try (var fin = Files.newBufferedWriter(filename)) {
            var writer = new Configuration.ConfigurationWriter(fin);
            writer.printValue(config);
        } catch (IOException ex) {
            LOGGER.info("Could not write recent files list ", ex);
        }
    }

    public void save() {
        store(PathConfig.getRecentFileStorage());
    }

    public class RecentFileEntry {
        public static final String KEY_PATH = "path";
        public static final String KEY_PROFILE = "profile";
        public static final String KEY_OPTIONS = "options";
        private static final String KEY_LOAD_SINGLE_JAVA = "singleJava";

        private @Nullable JMenuItem menuItem;

        private final String path;
        private final @Nullable String profile;
        private final boolean singleJava;
        private final @Nullable Configuration additionalOption;

        public RecentFileEntry(String path, @Nullable String profile, boolean singleJava,
                @Nullable Configuration additionalOption) {
            this.additionalOption = additionalOption;
            this.path = path;
            this.profile = profile;
            this.singleJava = singleJava;
        }

        public RecentFileEntry(Configuration options) {
            this(Objects.requireNonNull(options.getString(KEY_PATH)),
                options.getString(KEY_PROFILE),
                options.getBool(KEY_LOAD_SINGLE_JAVA, false),
                options.getTable(KEY_OPTIONS));
        }

        public Configuration asConfiguration() {
            Configuration config = new Configuration();
            config.set(KEY_PATH, path);
            config.set(KEY_PROFILE, profile);
            config.set(KEY_LOAD_SINGLE_JAVA, singleJava);
            config.set(KEY_OPTIONS, additionalOption);
            return config;
        }

        public String getAbsolutePath() {
            return path;
        }

        public JMenuItem createMenuItem() {
            if (menuItem == null) {
                menuItem = new JMenuItem(new RecentFileAction(this));
            }
            return menuItem;
        }
    }

    private class RecentFileAction extends KeyAction {
        private final RecentFileEntry recentFileEntry;

        public RecentFileAction(RecentFileEntry recentFileEntry) {
            this.recentFileEntry = recentFileEntry;
            setName(recentFileEntry.getAbsolutePath());
            setTooltip(recentFileEntry.getAbsolutePath());
        }

        @Override
        public void actionPerformed(ActionEvent actionEvent) {
            String absPath = recentFileEntry.getAbsolutePath();
            Path file = Paths.get(absPath);

            // special case proof bundles -> allow to select the proof to load
            if (ProofSelectionDialog.isProofBundle(file)) {
                Path proofPath = ProofSelectionDialog.chooseProofToLoad(file);
                if (proofPath == null) {
                    // canceled by user!
                } else {
                    mediator.getUI().loadProofFromBundle(file, proofPath);
                }
            } else {
                mediator.getUI().loadProblem(file);
            }
        }
    }
}
