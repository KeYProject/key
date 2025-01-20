/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.control;

import java.io.*;
import java.nio.charset.StandardCharsets;
import java.util.*;

import de.uka.ilkd.key.control.instantiation_model.TacletFindModel;
import de.uka.ilkd.key.control.instantiation_model.TacletInstantiationModel;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.settings.PathConfig;

public class InstantiationFileHandler {
    private static final String INSTANTIATION_DIR =
        PathConfig.getKeyConfigDir() + File.separator + "instantiations";

    private static final String SEPARATOR1 = "<<<<<<";

    private static final String SEPARATOR2 = ">>>>>>";

    private static final String LINE_END = System.getProperty("line.separator");

    private static final int SAVE_COUNT = 5;

    private static HashMap<String, List<List<String>>> hm;

    public static boolean hasInstantiationListsFor(Taclet taclet) {
        if (hm == null) {
            createHashMap();
        }
        return hm.containsKey(taclet.name().toString());
    }

    public static java.util.List<List<String>> getInstantiationListsFor(Taclet taclet) {
        if (hasInstantiationListsFor(taclet)) {
            if (hm.get(taclet.name().toString()) == null) {
                createListFor(taclet);
            }
            return hm.get(taclet.name().toString());
        }
        return null;
    }

    private static void createHashMap() {
        File dir = new File(INSTANTIATION_DIR);
        if (!dir.exists()) {
            dir.mkdirs();
        }
        String[] instFiles = dir.list();
        if (instFiles == null) {
            hm = new LinkedHashMap<>(0);
        } else {
            // Avoid resizing of HashMap
            hm = new LinkedHashMap<>(instFiles.length + 1, 1);
            for (String instFile : instFiles) {
                hm.put(instFile, null);
            }
        }
    }

    private static void createListFor(Taclet taclet) {
        java.util.List<List<String>> instList = new LinkedList<>();
        java.util.List<String> instantiations = new LinkedList<>();
        try (BufferedReader br = new BufferedReader(
            new FileReader(INSTANTIATION_DIR + File.separator + taclet.name().toString(),
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
        java.util.List<List<String>> instList = getInstantiationListsFor(taclet);
        try (BufferedWriter bw = new BufferedWriter(
            new FileWriter(INSTANTIATION_DIR + File.separator + taclet.name().toString(),
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
