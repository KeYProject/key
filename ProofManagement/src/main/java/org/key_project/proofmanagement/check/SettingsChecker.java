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
 * This class checks if the settings of the given proof bundles are consistent.
 */
public class SettingsChecker implements Checker {

    //TODO: maybe make something Java 8 compatible here
    //TODO: it is not checked that this is a equivalence relation, but thats probably okay.
    // Setting not explicitly listed here are assumed to be compatible iff equal
    private static final Map<String, Set<Set<String>>> choiceCompatibilityClasses = new HashMap<String, Set<Set<String>>>();
//            Map.ofEntries(
//            Map.entry("moreSeqRules", Set.of(Set.of("moreSeqRules:off", "moreSeqRules:on")))
//            );



    //TODO: Carry file info with the data to allow for good user feedback
    //TODO: Consistency Checker should work on a higher abstraction level and not handle files, do file handling separately (we'll also need to reuse that)
    @Override
    public CheckerData check(List<Path> proofFiles, CheckerData currentRes) {

        List<KeYUserProblemFile> problemFiles = new ArrayList<>();

        for (Path p : proofFiles) {
            problemFiles.add(new KeYUserProblemFile(p.toString(), p.toFile(),
                    new TrivialFileRepo(), ProgressMonitor.Empty.getInstance(), AbstractProfile.getDefaultProfile(), false));
        }


        List<ProofSettings> proofSettings = new ArrayList<>();

        for (KeYUserProblemFile f : problemFiles) {
            try {
                proofSettings.add(f.readPreferences());
            } catch (ProofInputException e) {
                e.printStackTrace();
            }
        }

        // TODO: messages
        CheckerData result = new CheckerData(consistent(proofSettings), currentRes.getPbh());
        return result;
    }

    //TODO: SMT settings ignored for now! (strategy settings should be irrelevant)
    public static boolean consistent(List<ProofSettings> proofSettings) {
        List<ChoiceSettings> choiceSettings = new ArrayList<>();
        for (ProofSettings settings : proofSettings) {
            choiceSettings.add(settings.getChoiceSettings());
        }

        return choiceConsistent(choiceSettings);
    }

    private static boolean choiceConsistent(List<ChoiceSettings> choiceSettings) {
        //TODO this does not yet work as intended
        ChoiceSettings reference = choiceSettings.get(0);
        for (int i = 1; i < choiceSettings.size(); i++) {
            ChoiceSettings cs = choiceSettings.get(i);
            if (!cs.getDefaultChoices().keySet().equals(reference.getDefaultChoices().keySet())) {
                return false;
            }
            //TODO: check what kind of choices getChoices (not getDefaultChoices)returns, whether that is used at all and how it matters to us
            for (String key: reference.getDefaultChoices().keySet()) {
                if (!compatible(new Choice(new Name(key), reference.getDefaultChoices().get(key)), new Choice(new Name(key), cs.getDefaultChoices().get(key)))) {
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
