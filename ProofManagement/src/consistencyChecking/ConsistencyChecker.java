package consistencyChecking;

import java.nio.file.Path;
import java.util.Map;
import java.util.Set;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

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
public class ConsistencyChecker implements Checker{

    //TODO: maybe make something Java 8 compatible here
    //TODO: it is not checked that this is a equivalence relation, but thats probably okay.
    // Setting not explicitly listed here are assumed to be compatible iff equal
    private static final Map<String, Set<Set<String>>> choiceCompatibilityClasses = Map.ofEntries(
            Map.entry("moreSeqRules", Set.of(Set.of("moreSeqRules:off", "moreSeqRules:on")))
            );



    //TODO: Carry file info with the data to allow for good user feedback
    //TODO: Consistency Checker should work on a higher abstraction level and not handle files, do file handling separately (we'll also need to reuse that)
    @Override
    public boolean check(ImmutableList<Path> proofFiles) {

        ImmutableList<KeYUserProblemFile> problemFiles = ImmutableSLList.nil();

        for (Path p : proofFiles) {
            problemFiles = problemFiles.append(new KeYUserProblemFile(p.toString(), p.toFile(),
                    new TrivialFileRepo(), ProgressMonitor.Empty.getInstance(), AbstractProfile.getDefaultProfile(), false));
        }


        ImmutableList<ProofSettings> proofSettings = ImmutableSLList.nil();

        for (KeYUserProblemFile f : problemFiles) {
            try {
                proofSettings = proofSettings.append(f.readPreferences());
            }
            catch (ProofInputException e) {
                e.printStackTrace();
            }
        }

        return consistent(proofSettings);
    }

    //TODO: SMT settings ignored for now! (strategy settings should be irrelevant)
    public static boolean consistent(ImmutableList<ProofSettings> proofSettings) {
        ImmutableList<ChoiceSettings> choiceSettings = ImmutableSLList.nil();
        for (ProofSettings settings : proofSettings) {
            choiceSettings = choiceSettings.append(settings.getChoiceSettings());
        }

        return choiceConsistent(choiceSettings);
    }

    private static boolean choiceConsistent(ImmutableList<ChoiceSettings> choiceSettings) {
        //TODO this does not yet work as intended
        ChoiceSettings reference = choiceSettings.head();
        for (ChoiceSettings cs: choiceSettings.tail()) {
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
