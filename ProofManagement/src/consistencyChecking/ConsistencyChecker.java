package consistencyChecking;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.List;
import java.util.stream.Collectors;

import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;
import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.consistency.DiskFileRepo;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.settings.ChoiceSettings;
import de.uka.ilkd.key.settings.ProofSettings;
import de.uka.ilkd.key.util.ProgressMonitor;

public class ConsistencyChecker {

    //TODO: Consistency Checker should work on a higher abstraction level and not handle files
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


        List<Path> proofFiles = null;
        try {
            proofFiles = Files.list(tmpDir).filter(name -> name.getFileName().toString().toLowerCase().endsWith(".proof")).collect(Collectors.toList());
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

        for (ProofSettings settings : proofSettings) {

            System.out.println(settings.settingsToString());

            //System.out.println(settings.getChoiceSettings().getDefaultChoices().get("assertions"));
            //System.out.println(settings.getChoiceSettings().getChoices());
        }


        return consistent(proofSettings);
    }

    public static boolean consistent(ImmutableList<ProofSettings> proofSettings) {
        ImmutableList<ChoiceSettings> choiceSettings = ImmutableSLList.nil();
        for (ProofSettings settings : proofSettings) {
            choiceSettings = choiceSettings.append(settings.getChoiceSettings());
        }

        return choiceConsistent(choiceSettings);
    }

    private static boolean choiceConsistent(ImmutableList<ChoiceSettings> choiceSettings) {
        //TODO this does not yet work as intended
        for (ChoiceSettings cs: choiceSettings) {
            if (!( cs.getDefaultChoices().equals(choiceSettings.head().getDefaultChoices())
                    || cs.getChoices().equals(choiceSettings.head().getChoices()))) {
                return false;
            }
        }
        return true;
    }

}
