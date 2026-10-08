/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.gui.fx.recentfiles;

import java.io.BufferedWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

import de.uka.ilkd.key.gui.fx.actions.QuickSaveF;
import de.uka.ilkd.key.nparser.ParsingFacade;
import de.uka.ilkd.key.settings.Configuration;
import de.uka.ilkd.key.settings.PathConfig;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * The recent files store of the JavaFX UI, the counter-part of
 * {@code de.uka.ilkd.key.gui.RecentFileMenu} in the Swing module {@code key.ui} (the menu UI
 * itself lives in {@code MainWindowF}).
 * <p>
 * The entries are persisted in the <b>same</b> file as the Swing UI
 * ({@code ~/.key/<version>/recentFiles_v2.json}, see {@link PathConfig.KeyPaths#recentFileStorage})
 * with the same JSON keys, so both UIs share one recent-files list. Like the Swing original, at
 * most {@value #MAX_RECENT_FILES} entries are kept, an already present path is moved to the front,
 * and only existing files are added.
 */
public final class RecentFilesF {

    private static final Logger LOGGER = LoggerFactory.getLogger(RecentFilesF.class);

    /**
     * The maximum number of recent files kept (Swing {@code RecentFileMenu.MAX_RECENT_FILES}).
     */
    public static final int MAX_RECENT_FILES = 8;

    private static final String KEY_PATH = "path";
    private static final String KEY_PROFILE = "profile";
    private static final String KEY_OPTIONS = "options";
    private static final String KEY_LOAD_SINGLE_JAVA = "singleJava";

    /**
     * One recent file entry; the fields mirror the Swing {@code RecentFileEntry}.
     *
     * @param path absolute path of the file
     * @param profile ident of the profile the file was loaded with, {@code null} for the default
     * @param singleJava whether the file was loaded as a single Java file
     * @param additionalOption additional profile options, {@code null} if none
     */
    public record Entry(String path, String profile, boolean singleJava,
            Configuration additionalOption) {

        static Entry of(Configuration options) {
            return new Entry(Objects.requireNonNull(options.getString(KEY_PATH)),
                options.getString(KEY_PROFILE), options.getBool(KEY_LOAD_SINGLE_JAVA, false),
                options.getTable(KEY_OPTIONS));
        }

        Configuration asConfiguration() {
            Configuration config = new Configuration();
            config.set(KEY_PATH, path);
            // only store a real profile name; writing null serializes to "null", which fails to
            // resolve on reload (same comment as the Swing original)
            if (profile != null) {
                config.set(KEY_PROFILE, profile);
            }
            config.set(KEY_LOAD_SINGLE_JAVA, singleJava);
            config.set(KEY_OPTIONS, additionalOption);
            return config;
        }
    }

    /** most-recent-first */
    private final List<Entry> entries = new ArrayList<>();
    /** invoked after every model change, used by the main window to rebuild the menu */
    private Runnable onChange = () -> {
    };

    /**
     * Loads the entries from the current default configuration folder (falls back to the previous
     * version's folder like the Swing original).
     */
    public void load() {
        Path storage = PathConfig.currentPaths.recentFileStorage;
        if (!Files.exists(storage) && PathConfig.previousPaths != null) {
            storage = PathConfig.previousPaths.recentFileStorage;
        }
        if (!Files.exists(storage)) {
            return;
        }
        try {
            List<Configuration> stored = ParsingFacade.parseConfigurationFile(storage)
                    .asConfigurationList();
            entries.clear();
            String tmpFolder = System.getProperty("java.io.tmpdir");
            for (Configuration configuration : stored) {
                Entry entry = Entry.of(configuration);
                // silently drop vanished files of the temp folder (quick saves), like Swing
                if (entry.path().startsWith(tmpFolder) && !Files.exists(Path.of(entry.path()))) {
                    continue;
                }
                entries.add(entry);
            }
            fireChange();
        } catch (IOException e) {
            LOGGER.info("Could not read the recent files list {}", storage, e);
        } catch (Exception e) {
            LOGGER.error("Could not read the recent files list.", e);
        }
    }

    /**
     * Adds a new file to the beginning of the recent files list; an already present path is moved
     * to the front; non-existing files are silently ignored; the list is saved afterwards.
     *
     * @param path absolute path of the file
     */
    public void add(String path) {
        add(path, null, false, null);
    }

    /**
     * Adds a new file with the load options of the Swing original (profile, single Java file,
     * additional profile options).
     * <p>
     * The quick save location is never added (Swing {@code RecentFileMenu.addNewToModelAndView}:
     * "do not add quick save location to recent files").
     */
    public void add(String path, String profile, boolean singleJava,
            Configuration additionalOption) {
        if (QuickSaveF.QUICK_SAVE_PATH.endsWith(path)) {
            return;
        }
        Optional<Entry> existing = entries.stream().filter(it -> path.equals(it.path()))
                .findFirst();
        if (existing.isPresent()) {
            Entry entry = existing.get();
            entries.remove(entry);
            entries.addFirst(entry);
            fireChange();
            save();
            return;
        }
        if (!Files.exists(Path.of(path))) {
            return;
        }
        entries.addFirst(new Entry(path, profile, singleJava, additionalOption));
        while (entries.size() > MAX_RECENT_FILES) {
            entries.removeLast();
        }
        fireChange();
        save();
    }

    /**
     * @return the absolute path of the most recently opened file, or {@code null} if the list is
     *         empty
     */
    public String getMostRecent() {
        return entries.isEmpty() ? null : entries.getFirst().path();
    }

    /**
     * @return an immutable copy of the entries, most-recent-first
     */
    public List<Entry> getEntries() {
        return List.copyOf(entries);
    }

    /**
     * Registers the hook invoked after every model change (on the FX thread; all mutators must be
     * called on the FX thread).
     *
     * @param hook the hook, may be {@code null} to clear it
     */
    public void setOnChange(Runnable hook) {
        onChange = hook != null ? hook : () -> {
        };
    }

    private void fireChange() {
        onChange.run();
    }

    private void save() {
        List<Configuration> stored =
            entries.stream().map(Entry::asConfiguration).toList();
        try (BufferedWriter writer =
            Files.newBufferedWriter(PathConfig.currentPaths.recentFileStorage)) {
            new Configuration.ConfigurationWriter(writer).printValue(stored);
        } catch (IOException e) {
            LOGGER.info("Could not write the recent files list "
                + PathConfig.currentPaths.recentFileStorage, e);
        }
    }

    /**
     * Short unique display names for the given paths (Swing {@code ShortUniqueFileNames}): each
     * name starts as the file name and is extended by parent directory segments (from the end of
     * the path) until all names are distinct.
     *
     * @param paths the paths, in display order
     * @return one display name per path
     */
    public static List<String> uniqueNames(List<String> paths) {
        int size = paths.size();
        String[][] segments = new String[size][];
        for (int i = 0; i < size; i++) {
            segments[i] = paths.get(i).replace('\\', '/').split("/");
        }
        int[] depth = new int[size];
        Arrays.fill(depth, 1);
        boolean changed = true;
        while (changed) {
            changed = false;
            for (int i = 0; i < size; i++) {
                for (int j = i + 1; j < size; j++) {
                    if (!name(segments[i], depth[i]).equals(name(segments[j], depth[j]))) {
                        continue;
                    }
                    boolean iCanGrow = depth[i] < segments[i].length;
                    boolean jCanGrow = depth[j] < segments[j].length;
                    if (!iCanGrow && !jCanGrow) {
                        continue; // identical full paths cannot be disambiguated
                    }
                    // grow the one with the shorter displayed name first
                    if (iCanGrow && jCanGrow) {
                        if (name(segments[i], depth[i]).length() <= name(segments[j],
                            depth[j]).length()) {
                            depth[i]++;
                        } else {
                            depth[j]++;
                        }
                    } else if (iCanGrow) {
                        depth[i]++;
                    } else {
                        depth[j]++;
                    }
                    changed = true;
                }
            }
        }
        List<String> names = new ArrayList<>(size);
        for (int i = 0; i < size; i++) {
            names.add(name(segments[i], depth[i]));
        }
        return names;
    }

    /**
     * @return the last {@code depth} segments of the path joined by '/'
     */
    private static String name(String[] segments, int depth) {
        StringBuilder name = new StringBuilder();
        for (int i = Math.max(0, segments.length - depth); i < segments.length; i++) {
            if (name.length() > 0) {
                name.append('/');
            }
            name.append(segments[i]);
        }
        return name.toString();
    }
}
