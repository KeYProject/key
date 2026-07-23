/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.control;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.*;

import de.uka.ilkd.key.control.instantiation_model.TacletFindModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.PathConfig;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

public class InstantiationFileHandler {
    private static final Logger LOGGER = LoggerFactory.getLogger(InstantiationFileHandler.class);

    private static final Path INSTANTIATION_DIR = getStoragePath();

    private static final String SEPARATOR1 = "<<<<<<";

    private static final String SEPARATOR2 = ">>>>>>";

    private static final String LINE_END = System.lineSeparator();

    private static final int SAVE_COUNT = 5;


    private static Map<String, List<List<String>>> hm;

    /// Finds the current place to store used instantiation. If there was a version switch
    /// (the folder does not exist), this method tries to copy previous instantiations to
    /// the new directory silently.
    ///
    /// It is guaranteed, that the folder exists.
    private static Path getStoragePath() {
        Path cur = PathConfig.currentPaths.keyConfigDir.resolve("instantiations");
        if (Files.exists(cur)) {
            return cur;
        }

        Path prev = PathConfig.previousPaths.keyConfigDir.resolve("instantiations");
        if (Files.exists(prev)) {
            try {
                Files.createDirectories(cur);
                try (var files = Files.walk(prev)) {
                    files.forEach(path -> {
                        try {
                            Files.copy(path, cur.resolve(path.relativize(prev)));
                        } catch (IOException ignore) {
                        }
                    });
                }
            } catch (IOException ignore) {
            }
        }
        return cur;
    }

    public static boolean hasInstantiationListsFor(Taclet taclet) {
        if (hm == null) {
            createHashMap();
        }
        return hm.containsKey(taclet.name().toString());
    }

    public static List<List<String>> getInstantiationListsFor(Taclet taclet) {
        if (hasInstantiationListsFor(taclet)) {
            if (hm.get(taclet.name().toString()) == null) {
                createListFor(taclet);
            }
            return hm.get(taclet.name().toString());
        }
        return null;
    }

    private static void createHashMap() {
        hm = new TreeMap<>();
        try (var stream = Files.list(INSTANTIATION_DIR)) {
            // using a TreeMap here avoids non-determinsm introduce by the file system.
            stream.forEach(file -> hm.put(file.toString(), null));
        } catch (IOException e) {
            LOGGER.warn("Could not read the instantions folder {}", INSTANTIATION_DIR, e);
        }
    }

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
