package de.uka.ilkd.key.gui;

import java.io.File;
import java.io.IOException;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.util.MiscTools;

// TODO: What FileRepo implementations should this work with? all?
//       How to create the correct Zip-Structure for TrivialFileRepo then?
// TODO: additional gui-button save bundle
/**
 * This class is responsible for saving (zipped) proof packages.
 * These packages contain all data needed for successfully reloading the proofs:
 * <ul>
 *  <li>.key files</li>
 *  <li>.proof files</li>
 *  <li>Java Source files (including additional files from classpath)</li>
 * </ul>
 * Not included are internal rule files of KeY.
 *
 * @author Wolfram Pfeifer
 */
public class ProofPackageSaver extends ProofSaver {

    /**
     * Creates a new ProofPackageSaver.
     * @param proof the proof to save
     * @param fileName the target filename
     * @param internalVersion the internal KeY version
     */
    public ProofPackageSaver(Proof proof, String fileName, String internalVersion) {
        super(proof, fileName, internalVersion);
    }

    @Override
    protected void save(File file) throws IOException {
        // get the FileRepo from the InitConfig of the Proof
        FileRepo repo = proof.getInitConfig().getFileRepo();

        /* create a filename for the actual proof file in the FileRepo:
         * We always use the contract name here (preparation for proof bundle
         * -> multiple proofs in one package). */
        String proofFileName = MiscTools.toValidFileName(proof.name().toString() + ".proof");

        // save the proof file to the FileRepo (stream is closed by the save method!)
        super.save(repo.createOutputStream(new File(proofFileName).toPath()));

        // save proof package with the help of the FileRepo
        repo.saveProof(file.toPath(), proof);
    }
}
