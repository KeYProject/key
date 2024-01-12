/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.proofmanagement.check;

import java.nio.file.Path;
import java.util.*;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.io.consistency.TrivialFileRepo;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProgressMonitor;

import org.key_project.proofmanagement.io.LogLevel;
import org.key_project.proofmanagement.io.ProofBundleHandler;

// TODO: precise user feedback

/**
 * This class checks if the settings of the given proofs are consistent.
 *
 * @author Jonas Krämer
 * @author Wolfram Pfeifer
 */
public class SettingsChecker implements Checker {

    // TODO: it is not checked that this is a equivalence relation, but thats probably okay.
    // Setting not explicitly listed here are assumed to be compatible iff equal
    private static final Map<String, Set<Set<String>>> choiceCompatibilityClasses = new HashMap<>();

    static {
        String[] strings = { "moreSeqRules:off", "moreSeqRules:on" };
        Set<String> inner = new HashSet<>(Arrays.asList(strings));
        Set<Set<String>> outer = Collections.singleton(inner);
        choiceCompatibilityClasses.put("moreSeqRules", outer);
    }

    // TODO: Carry file info with the data to allow for good user feedback
    @Override
    public void check(ProofBundleHandler pbh, CheckerData data) throws ProofManagementException {
        data.addCheck("settings");
        data.print("Running settings checker ...");

        // TODO: we should use the field of data.proofEntries
        // create a new KeYUserProblemFile for each path
        List<KeYUserProblemFile> problemFiles = new ArrayList<>();
        for (Path p : pbh.getProofFiles()) {
            problemFiles.add(new KeYUserProblemFile(p.toString(), p.toFile(),
                new TrivialFileRepo(), ProgressMonitor.Empty.getInstance(),
                AbstractProfile.getDefaultProfile(), false));
        }

        // parse the settings of each proof file
        List<ProofSettings> proofSettings = new ArrayList<>();
        for (KeYUserProblemFile f : problemFiles) {
            proofSettings.add(f.readPreferences());
        }

        // actual consistency check of the settings
        if (consistent(proofSettings, data)) {
            data.setSettingsState(CheckerData.SettingsState.CONSISTENT);
            data.print(LogLevel.INFO, "All settings are consistent!");
        } else {
            data.setSettingsState(CheckerData.SettingsState.INCONSISTENT);
            data.print(LogLevel.WARNING, "Incompatible settings found!");
        }
        data.print(LogLevel.INFO, "Settings check completed!");
    }

    /*
     * notes:
     * - every unique set of settings gets an id
     * - id is stored inside proof entry
     * - mapping from id to set of settings is shown in a table below the proof lines
     * - sets of settings are checked for compatibility (equivalence classes)
     * - settings inconsistent to the first one are marked red in proof line, others green
     */

    // TODO: SMT settings ignored for now! (strategy settings should be irrelevant)
    private static boolean consistent(List<ProofSettings> proofSettings, CheckerData data) {

        // TODO change to map Settings -> ProofEntry (for feedback)
        // extract ChoiceSettings from ProofSettings and check for compatibility
        List<ChoiceSettings> choiceSettings = new ArrayList<>();
        for (ProofSettings settings : proofSettings) {
            choiceSettings.add(settings.getChoiceSettings());
        }
        return choicesConsistent(choiceSettings, data);
    }

    private static boolean choicesConsistent(List<ChoiceSettings> choiceSettings,
            CheckerData data) {
        if (choiceSettings.isEmpty()) {
            return true;
        }

        boolean consistent = true;

        // store reference settings in data with id 0
        ChoiceSettings reference = choiceSettings.get(0);
        Map<String, String> refChoices = reference.getDefaultChoices();
        data.addReferenceChoices(refChoices);
        data.print(LogLevel.DEBUG, "Reference settings (id 0) are: " + refChoices);

        for (int i = 1; i < choiceSettings.size(); i++) {
            Map<String, String> cs = choiceSettings.get(i).getDefaultChoices();

            // settings are only added (with fresh id) if they are unique currently
            if (!data.getChoices2Id().containsKey(cs)) {
                // add to settings map with next free id
                data.addReferenceChoices(cs);

                data.print(LogLevel.DEBUG, "Found (currently) unique settings (assigned id " +
                    data.getChoices2Id().get(cs) + "): " + cs);

                // at least one of the entries is different:
                // in this case we have to check if all entries are compatible
                // (w.r.t. the compatibility classes defined above)
                if (!cs.keySet().equals(refChoices.keySet())) {
                    // one of them has a setting with an additional key

                    // do not return directly to compare other settings too
                    // return false;
                    consistent = false;
                    data.print(LogLevel.DEBUG, "Incompatible (additional key found)!");
                }
                for (String key : refChoices.keySet()) {
                    if (!compatible(new Choice(new Name(key), refChoices.get(key)),
                        new Choice(new Name(key), cs.get(key)))) {
                        // found at least one different value

                        // do not return directly to compare other settings too
                        // return false;
                        consistent = false;
                        data.print(LogLevel.DEBUG, "Incompatible (different values found)!");
                    }
                }
            } else {
                // add a map entry for lookup
                data.addChoices(cs);
                // settings from cs are identical to reference
                data.print(LogLevel.DEBUG, "These settings already exist (with id " +
                    data.getChoices2Id().get(cs) + "): " + cs);
            }
        }
        return consistent;
    }

    private static boolean compatible(Choice a, Choice b) {
        if (!a.name().equals(b.name())) {
            return false;
        }
        if (a.category().equals(b.category())) {
            return true;
        }

        if (choiceCompatibilityClasses.containsKey(a.name().toString())) {

            for (Set<String> compatibilityClass : choiceCompatibilityClasses
                    .get(a.name().toString())) {

                if (compatibilityClass.contains(a.category())
                        && compatibilityClass.contains(b.category())) {
                    return true;
                }
            }
        }
        return false;
    }
}
