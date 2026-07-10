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
import java.util.*;
import javax.swing.*;

import de.uka.ilkd.key.gui.actions.KeyAction;
import de.uka.ilkd.key.gui.fonticons.IconFactory;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.proof.init.DefaultProfileResolver;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;

import com.google.common.html.HtmlEscapers;
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

    private final MainWindow mainWindow;

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
    public RecentFileMenu(final MainWindow mediator) {
        this.mainWindow = mediator;
        this.menu = new JMenu("Recent Files");
        this.maxNumberOfEntries = MAX_RECENT_FILES;

        // menu.setEnabled(menu.getItemCount() != 0);
        menu.setIcon(IconFactory.recentFiles(16));

        if (Files.exists(PathConfig.currentPaths.recentFileStorage)) {
            loadFrom(PathConfig.currentPaths.recentFileStorage);
        } else {
            loadFrom(PathConfig.previousPaths.recentFileStorage);
        }
    }

    private void insertFirstEntry(RecentFileEntry entry) {
        menu.insert(entry.createMenuItem(), 0);
        mostRecentFile = entry;
        recentFiles.addFirst(entry);
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
            var entry = new RecentFileEntry(path, profile != null ? profile.ident() : null,
                singleJava, additionalOption);
            insertFirstEntry(entry);

            // Recalculate unique names
            computeShortestUniqueFilenames();
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
            if (!Files.exists(filename)) {
                return;
            }

            var file = ParsingFacade.parseConfigurationFile(filename);
            List<Configuration> recent = file.asConfigurationList();
            this.recentFiles.clear();
            this.mostRecentFile = null;

            String tmpFolder = System.getProperty("java.io.tmpdir");
            for (var c : recent) {
                final var e = new RecentFileEntry(c);

                // if file not present, and it was stored in the tmp folder,
                // we allow us to silently ignore it.
                if (e.path.startsWith(tmpFolder) && !Files.exists(Paths.get(e.path))) {
                    continue;
                }

                // The list is stored most-recent-first, so the first entry is the most recent.
                // (Previously this condition was inverted and overwrote mostRecentFile with every
                // entry, leaving it null after startup -- issue #3711.)
                if (mostRecentFile == null) {
                    mostRecentFile = e;
                }
                recentFiles.add(e);
                menu.add(e.createMenuItem());
            }

            computeShortestUniqueFilenames();
        } catch (FileNotFoundException ex) {
            LOGGER.info("Could not read RecentFileList. Did not find file {}", filename);
        } catch (IOException ioe) {
            LOGGER.error("Could not read RecentFileList. Some IO Error occured ", ioe);
        } catch (Exception ioe) {
            LOGGER.error("Could not read RecentFileList.", ioe);
        }
    }

    /**
     * @return the absolute path to the most recently opened file (maybe null)
     */
    @Nullable
    public String getMostRecent() {
        return mostRecentFile != null ? mostRecentFile.getAbsolutePath() : null;
    }

    private void computeShortestUniqueFilenames() {
        var map = new TreeMap<String, String>();
        var actions = new ArrayList<RecentFileAction>();

        for (var menuComponent : menu.getMenuComponents()) {
            var action = ((RecentFileAction) ((JMenuItem) menuComponent).getAction());
            map.put(action.fileEntry.path, action.fileEntry.path);
            actions.add(action);
        }

        var seq = map.keySet().stream().toList();
        var names = ShortUniqueFileNames.makeUniqueNames(seq);
        for (int i = 0; i < seq.size(); i++) {
            map.put(seq.get(i), names[i].getName());
        }

        for (RecentFileAction a : actions) {
            var p = a.fileEntry.profile;
            var option = a.fileEntry.additionalOption;
            a.putValue(Action.NAME, map.get(a.fileEntry.path) +
                    ((p == null || p.equals("null")) ? "" : " (Profile: %s)".formatted(p)));

            a.putValue(Action.SHORT_DESCRIPTION,
                "<html>" + HtmlEscapers.htmlEscaper().escape(a.fileEntry.path) +
                    (option == null ? "" : "<br>" + option)
                    + "</html>");
        }
    }


    /**
     * write the recent file names to the given properties file. the file will be read (if it
     * exists) and then re-written so no information will be lost.
     */
    public void store(Path filename) {
        List<Configuration> config =
            recentFiles.stream().map(RecentFileEntry::asConfiguration)
                    .toList();
        try (var fin = Files.newBufferedWriter(filename)) {
            var writer = new Configuration.ConfigurationWriter(fin);
            writer.printValue(config);
        } catch (IOException ex) {
            LOGGER.info("Could not write recent files list ", ex);
        }
    }

    public void save() {
        store(PathConfig.currentPaths.recentFileStorage);
    }

    public List<RecentFileEntry> getEntries() {
        return this.recentFiles;
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

        public RecentFileEntry(
                String path,
                @Nullable String profile,
                boolean singleJava,
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
            // Only store a real profile name; writing a null serializes to the string "null", which
            // then fails to resolve on reload.
            if (profile != null) {
                config.set(KEY_PROFILE, profile);
            }
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
        private final RecentFileEntry fileEntry;

        public RecentFileAction(RecentFileEntry fileEntry) {
            this.fileEntry = fileEntry;
            setName(fileEntry.getAbsolutePath());
            setTooltip(fileEntry.getAbsolutePath());
        }

        @Override
        public void actionPerformed(ActionEvent actionEvent) {
            String absPath = fileEntry.getAbsolutePath();
            Path file = Paths.get(absPath);

            // special case proof bundles -> allow to select the proof to load
            if (ProofSelectionDialog.isProofBundle(file)) {
                Path proofPath = ProofSelectionDialog.chooseProofToLoad(file);
                if (proofPath == null) {
                    // canceled by user!
                } else {
                    mainWindow.loadProofFromBundle(file, proofPath);
                }
            } else {
                String profileName = fileEntry.profile;
                // A missing profile -- null, or the literal string "null" that older recent-file
                // entries stored for it -- means "use the default profile", not an error.
                boolean hasProfile = profileName != null && !profileName.equals("null");
                var selectedProfile = hasProfile
                        ? ServiceLoader.load(DefaultProfileResolver.class)
                                .stream()
                                .filter(it -> it.get().getProfileName().equals(profileName))
                                .findFirst()
                                .map(it -> it.get().getDefaultProfile())
                        : Optional.<Profile>empty();

                if (hasProfile && selectedProfile.isEmpty()) {
                    JOptionPane.showMessageDialog(mainWindow,
                        "Could not find previous selected profile %s.".formatted(profileName));
                    return;
                }

                var profile = selectedProfile.orElse(null);
                var additionalProfileOptions = fileEntry.additionalOption;

                mainWindow.loadProblem(file, pl -> {
                    if (profile != null) {
                        pl.setProfileOfNewProofs(profile);
                        pl.setAdditionalProfileOptions(additionalProfileOptions);
                    }
                    pl.setLoadSingleJavaFile(fileEntry.singleJava);
                });
            }
        }
    }
}
