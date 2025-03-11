/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;
import java.nio.file.Paths;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.consistency.AbstractFileRepo;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.util.MiscTools;

/**
 * This class is responsible for saving (zipped) proof bundles. These bundles contain all data
 * needed for successfully reloading the proofs:
 * <ul>
 * <li>.key files</li>
 * <li>.proof files</li>
 * <li>Java Source files (including additional files from classpath)</li>
 * </ul>
 * Not included are internal rule files of KeY.
 *
 * @author Wolfram Pfeifer
 */
public class ProofBundleSaver extends ProofSaver {

    /**
     * Creates a new ProofBundleSaver.
     *
     * @param proof the proof to save
     * @param saveFile the target filename
     */
    public ProofBundleSaver(Proof proof, File saveFile) {
        super(proof, saveFile);
    }

    @Override
    protected void save(File file) throws IOException {
        // get the FileRepo from the InitConfig of the Proof
        FileRepo repo = proof.getInitConfig().getFileRepo();

        // this ProofSaver can not be used with TrivialFileRepo
        if (!(repo instanceof AbstractFileRepo)) {
            throw new UnsupportedOperationException(
                "Error! This FileRepo does not support" + "bundle saving!");
        }

        /*
         * create a filename for the actual proof file in the FileRepo: We always use the contract
         * name here (preparation for proof bundle -> saving multiple proofs).
         */
        String proofFileName = MiscTools.toValidFileName(proof.name().toString() + ".proof");

        // save the proof file to the FileRepo (stream is closed by the save method!)
        save(repo.createOutputStream(Paths.get(proofFileName)));

        // save proof bundle with the help of the FileRepo
        ((AbstractFileRepo) repo).saveProof(file.toPath());
    }
}
