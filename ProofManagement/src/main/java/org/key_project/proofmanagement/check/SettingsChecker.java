package org.key_project.proofmanagement.check;

import java.nio.file.Path;
import java.util.*;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.consistency.TrivialFileRepo;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProgressMonitor;

//TODO: precise user feedback

/**
 * This class checks if the settings of the given proofs are consistent.
 *
 * @author Jonas Krämer
 * @author Wolfram Pfeifer
 */
public class SettingsChecker implements Checker {

    //TODO: it is not checked that this is a equivalence relation, but thats probably okay.
    // Setting not explicitly listed here are assumed to be compatible iff equal
    private static final Map<String, Set<Set<String>>> choiceCompatibilityClasses = new HashMap<>();
//            Map.ofEntries(
//            Map.entry("moreSeqRules", Set.of(Set.of("moreSeqRules:off", "moreSeqRules:on")))
//            );
    static {
        String[] strings = {"moreSeqRules:off", "moreSeqRules:on"};
        Set<String> inner = new HashSet<>(Arrays.asList(strings));
        Set<Set<String>> outer = Collections.singleton(inner);
        choiceCompatibilityClasses.put("moreSeqRules", outer);
    }

    //TODO: Carry file info with the data to allow for good user feedback
    @Override
    public void check(List<Path> proofFiles, CheckerData data) throws ProofManagementException {
        data.addCheck("settings");
        data.print("Running settings checker ...");

        // create a new KeYUserProblemFile for each path
        List<KeYUserProblemFile> problemFiles = new ArrayList<>();
        for (Path p : proofFiles) {
            problemFiles.add(new KeYUserProblemFile(p.toString(), p.toFile(),
                new TrivialFileRepo(), ProgressMonitor.Empty.getInstance(),
                AbstractProfile.getDefaultProfile(), false));
        }

        // parse the settings of each proof file
        List<ProofSettings> proofSettings = new ArrayList<>();
        for (KeYUserProblemFile f : problemFiles) {
            try {
                proofSettings.add(f.readPreferences());
            } catch (ProofInputException e) {
                throw new ProofManagementException("Proof settings could not be read from " + f
                        + System.lineSeparator() + e.toString());
            }
        }

        // actual consistency check of the settings
        if (!consistent(proofSettings, data)) {
            data.setConsistent(false);
        }
    }

    /* requirements:
     * - every unique set of settings gets an id
     * - id is stored inside proof entry
     * - mapping from id to set of settings is shown in a table below the proof lines
     * - sets of settings are checked for compatibility (equivalence classes)
     * - settings inconsistent to the first one are marked red in proof line, others green
     */

    //TODO: SMT settings ignored for now! (strategy settings should be irrelevant)
    private static boolean consistent(List<ProofSettings> proofSettings, CheckerData data) {

        // extract ChoiceSettings from ProofSettings and check for compatibility
        List<ChoiceSettings> choiceSettings = new ArrayList<>();
        for (ProofSettings settings : proofSettings) {
            choiceSettings.add(settings.getChoiceSettings());
        }
        return choicesConsistent(choiceSettings, data);
    }

    private static boolean choicesConsistent(List<ChoiceSettings> choiceSettings, CheckerData data) {
        // reference settings for each id
        //Map<HashMap<String, String>, Integer> uniqueSettings = new HashMap<>();

        //TODO this does not yet work as intended
        ChoiceSettings reference = choiceSettings.get(0);

        // TODO: at least one element
        assert reference != null;
        //uniqueSettings.put(reference.getDefaultChoices(), 0);
        data.addChoices(reference.getDefaultChoices(), 0);

        for (int i = 1; i < choiceSettings.size(); i++) {
            HashMap<String, String> cs = choiceSettings.get(i).getDefaultChoices();
            /*
            if (!uniqueSettings.containsKey(cs)) {
                // found new unique setting -> add
                uniqueSettings.put(cs, uniqueSettings.size());
            }
            */
            data.addChoices(cs, data.getChoices2Id().size()); // uniqueSettings.get(cs));

            if (!cs.keySet().equals(reference.getDefaultChoices().keySet())) {
                return false;
            }
            for (String key: reference.getDefaultChoices().keySet()) {
                data.addChoiceName(key);
                if (!compatible(new Choice(new Name(key), reference.getDefaultChoices().get(key)),
                                new Choice(new Name(key), cs.get(key)))) {
                    return false;
                }
            }
        }
        return true;
    }

    private static boolean compatible(Choice a, Choice b) {
        if (!a.name().equals(b.name())) {
            return false;
        }
        if (a.category().equals(b.category())) {
            return true;
        }

        if (choiceCompatibilityClasses.containsKey(a.name().toString())) {

            for (Set<String> compatibilityClass: choiceCompatibilityClasses.get(a.name().toString())) {

                if (compatibilityClass.contains(a.category()) && compatibilityClass.contains(b.category())){
                    return true;
                }
            }
        }
        return false;
    }
}
