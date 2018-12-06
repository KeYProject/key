package consistencyChecking;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;

import org.key_project.util.java.IOUtil;

import de.uka.ilkd.key.proof.init.AbstractProfile;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.io.KeYFile;
import de.uka.ilkd.key.proof.io.consistency.DiskFileRepo;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
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

        // create new KeYUserProblemFile pointing to the (unzipped) proof file
        Path unzippedProof = tmpDir.resolve(Paths.get("proof.proof"));

        KeYFile keyFile = new KeYUserProblemFile(unzippedProof.toString(), unzippedProof.toFile(),
                fileRepo, ProgressMonitor.Empty.getInstance(), AbstractProfile.getDefaultProfile(), false);


        ProofSettings settings = null;
        try {
            settings = keyFile.readPreferences();
        }
        catch (ProofInputException e) {
            e.printStackTrace();
        }

        //System.out.println(settings.settingsToString());

        //System.out.println(settings.getChoiceSettings().getDefaultChoices().get("assertions"));
        //System.out.println(settings.getChoiceSettings().getChoices());

        return false;

    }

}
