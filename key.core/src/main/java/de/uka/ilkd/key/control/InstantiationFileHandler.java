/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.control;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.*;
import java.util.*;

import de.uka.ilkd.key.control.instantiation_model.TacletFindModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.PathConfig;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

@NullMarked
public class InstantiationFileHandler {
    private static final Logger LOGGER = LoggerFactory.getLogger(InstantiationFileHandler.class);

    private static final Path INSTANTIATION_DIR = getStoragePath();

    private static final String SEPARATOR1 = "<<<<<<";

    private static final String SEPARATOR2 = ">>>>>>";

    private static final String LINE_END = System.lineSeparator();

    private static final int SAVE_COUNT = 5;


    /**
     * Lazily-initialized map from taclet name to its stored instantiation lists.
     * A {@code null} value marks an entry that is present but not (yet) loaded from disk.
     */
    private static @Nullable Map<String, @Nullable List<List<String>>> hm;

    /// Finds the current place to store used instantiations. If there was a version change
    /// (the folder does not exist), this method tries to copy previous instantiations to
    /// the new directory silently. However, if both old and new instantiations exist, they are not
    /// merge, i.e. only the new ones are used currently.
    /// <p>
    /// The current and previous key configuration directories are always set when the key
    /// settings have been loaded; the dereferences of the (nullable) configuration paths are
    /// suppressed with a scoped key.
    @SuppressWarnings("nullness:dereference.of.nullable")
    private static Path getStoragePath() {
        Path cur = PathConfig.currentPaths.keyConfigDir.resolve("instantiations");
        if (Files.exists(cur)) {
            /*
             * At the moment, we do not merge when old and new instantiations are
             * present. In the future, we could go one step further and try to merge.
             */
            return cur;
        }
        // create the directory for storing instantiations
        try {
            Files.createDirectories(cur);
        } catch (IOException e) {
            LOGGER.warn("Could not create the instantiations folder {}", cur, e);
        }

        // Check if instantiations from older key version exist. If so, try to copy them over.
        Path prev = PathConfig.previousPaths.keyConfigDir.resolve("instantiations");
        if (Files.exists(prev)) {
            try (var files = Files.walk(prev)) {
                files.forEach(path -> {
                    try {
                        Path target = cur.resolve(prev.relativize(path));
                        // Do not overwrite existing file!
                        if (!Files.exists(target)) {
                            Files.copy(path, target);
                        }
                    } catch (IOException inner) {
                        LOGGER.warn("Could not copy instantiation file {}", path, inner);
                    }
                });
            } catch (IOException e) {
                LOGGER.warn("Could not copy instantiation files from {} to {}", prev, cur, e);
            }
        }
        return cur;
    }

    /**
     * Returns whether instantiation lists have been stored for the given taclet.
     *
     * @param taclet The taclet to look up.
     * @return True iff an instantiation list entry exists for the taclet.
     *         <p>
     *         The instantiation map is lazily created on first access; the dereference of the
     *         (nullable)
     *         map is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public static boolean hasInstantiationListsFor(Taclet taclet) {
        if (hm == null) {
            createHashMap();
        }
        return hm.containsKey(taclet.name().toString());
    }

    /**
     * Returns the instantiation lists stored for the given taclet, creating the list lazily on
     * first access.
     *
     * @param taclet The taclet to look up.
     * @return The stored instantiation lists, or {@code null} if none are stored.
     *         <p>
     *         The instantiation map is lazily created on first access; the dereferences of the
     *         (nullable) map are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public static @Nullable List<List<String>> getInstantiationListsFor(Taclet taclet) {
        if (hasInstantiationListsFor(taclet)) {
            if (hm.get(taclet.name().toString()) == null) {
                createListFor(taclet);
            }
            return hm.get(taclet.name().toString());
        }
        return null;
    }

    /**
     * Creates the instantiation map from the stored instantiation files.
     * <p>
     * The map and the file names of the stored instantiation files are always present here; the
     * dereferences of the (nullable) map and file-name paths are suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    private static void createHashMap() {
        hm = new TreeMap<>();
        try (var stream = Files.list(INSTANTIATION_DIR)) {
            // using a TreeMap here avoids non-determinsm introduce by the file system.
            stream.forEach(file -> hm.put(file.getFileName().toString(), null));
        } catch (IOException e) {
            LOGGER.warn("Could not read the instantiations folder {}", INSTANTIATION_DIR, e);
        }
    }

    /**
     * Reads the stored instantiation list of the given taclet into the instantiation map.
     *
     * @param taclet The taclet whose stored instantiations are loaded.
     *        <p>
     *        The instantiation map is created before a list is stored into it; the dereference of
     *        the
     *        (nullable) map is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    private static void createListFor(Taclet taclet) {
        List<List<String>> instList = new LinkedList<>();
        List<String> instantiations = new LinkedList<>();
        try (BufferedReader br = new BufferedReader(
            new FileReader(INSTANTIATION_DIR + File.separator + taclet.name(),
                StandardCharsets.UTF_8))) {
            String line = br.readLine();
            StringBuilder sb = new StringBuilder();
            while (line != null) {
                if (line.equals(SEPARATOR1)) {
                    if (sb.length() > 0) {
                        instantiations.add(sb.toString());
                    }
                    sb = new StringBuilder();
                    if (instantiations.size() > 0) {
                        instList.add(instantiations);
                    }
                    instantiations = new LinkedList<>();
                } else if (line.equals(SEPARATOR2)) {
                    if (sb.length() > 0) {
                        instantiations.add(sb.toString());
                    }
                    sb = new StringBuilder();
                } else {
                    if (sb.length() > 0) {
                        sb.append(LINE_END);
                    }
                    sb.append(line);
                }
                line = br.readLine();
            }
            if (sb.length() > 0) {
                instantiations.add(sb.toString());
            }
        } catch (IOException e) {
        }
        if (instantiations.size() > 0) {
            instList.add(instantiations);
        }
        hm.put(taclet.name().toString(), instList);
    }

    /**
     * Saves the instantiation map of the given model.
     *
     * @param model The model whose instantiations are saved.
     *        <p>
     *        The instantiation map is created before a list is stored into it; the dereference of
     *        the
     *        (nullable) map is suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    public static void saveListFor(TacletInstantiationModel model) {
        Taclet taclet = model.taclet();
        TacletFindModel tableModel = model.tableModel();
        int start = model.tacletApp().instantiations().size();
        List<List<String>> instList = getInstantiationListsFor(taclet);
        try (BufferedWriter bw = new BufferedWriter(
            new FileWriter(INSTANTIATION_DIR + File.separator + taclet.name(),
                StandardCharsets.UTF_8))) {
            StringBuilder sb = new StringBuilder();
            for (int i = start; i < tableModel.getRowCount(); i++) {
                if (i > start) {
                    sb.append(SEPARATOR2).append(LINE_END);
                }
                sb.append(tableModel.getValueAt(i, 1)).append(LINE_END);
            }
            String newInst = sb.toString();
            bw.write(newInst);
            if (instList != null) {
                final ListIterator<List<String>> instListIt = instList.listIterator();
                int count = 1;
                while (instListIt.hasNext() && count < SAVE_COUNT) {
                    final ListIterator<String> instIt = instListIt.next().listIterator();
                    sb = new StringBuilder();
                    for (int i = 0; instIt.hasNext(); i++) {
                        if (i > 0) {
                            sb.append(SEPARATOR2).append(LINE_END);
                        }
                        sb.append(instIt.next()).append(LINE_END);
                    }
                    String oldInst = sb.toString();
                    if (!oldInst.equals(newInst)) {
                        bw.write(SEPARATOR1 + LINE_END + oldInst);
                        count++;
                    }
                }
            }
        } catch (IOException e) {
        }
        hm.put(taclet.name().toString(), null);
    }
}
