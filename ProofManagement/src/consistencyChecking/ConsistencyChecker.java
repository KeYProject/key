package consistencyChecking;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.logic.Choice;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.consistency.DiskFileRepo;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProgressMonitor;

//TODO: precise user feedback
public class ConsistencyChecker {

    //TODO: maybe make something Java 8 compatible here
    //TODO: it is not checked that this is a equivalence relation, but thats probably okay.
    // Setting not explicitly listed here are assumed to be compatible iff equal
    private static final Map<String, Set<Set<String>>> choiceCompatibilityClasses = Map.ofEntries(
            Map.entry("moreSeqRules-moreSeqRules", Set.of(Set.of("moreSeqRules:off", "moreSeqRules:on")))
            );



    //TODO: Carry file info with the data to allow for good user feedback
    //TODO: Consistency Checker should work on a higher abstraction level and not handle files, do file handling separately (we'll also need to reuse that)
    public static boolean consistent(String sPath) {
        Path path = Paths.get(sPath);

        Path tmpDir = null;
        FileRepo fileRepo = null;

        try {
            tmpDir = Files.createTempDirectory("KeYunzip");

            IOUtil.extractZip(path, tmpDir);

            fileRepo = new DiskFileRepo("HacKeYrepo");
        }
        catch (IOException e) {
            e.printStackTrace();
        }

        // point the FileRepo to the temporary directory
        fileRepo.setBaseDir(tmpDir);


        ImmutableList<Path> proofFiles = ImmutableSLList.nil();
        try {
            proofFiles = proofFiles.append(Files.list(tmpDir).filter(name -> name.getFileName().toString().toLowerCase().endsWith(".proof")).collect(Collectors.toList()));
        }
        catch (IOException e1) {
            e1.printStackTrace();
        }

        ImmutableList<KeYUserProblemFile> problemFiles = ImmutableSLList.nil();

        for (Path p : proofFiles) {
            problemFiles = problemFiles.append(new KeYUserProblemFile(p.toString(), p.toFile(),
                    fileRepo, ProgressMonitor.Empty.getInstance(), AbstractProfile.getDefaultProfile(), false));
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
                if (!compatible(new Choice(new Name(key), reference.getDefaultChoices().get(key)), new Choice(key, cs.getDefaultChoices().get(key)))) {
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

        for (Set<String> compatibilityClass: choiceCompatibilityClasses.get(a.name().toString())) {
            if (compatibilityClass.contains(a.category()) && compatibilityClass.contains(b.category())){
                return true;
            }
        }

        return false;
    }

}
