/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.proof.io;

import java.io.IOException;
import java.io.OutputStream;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Objects;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.consistency.AbstractFileRepo;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;
import de.uka.ilkd.key.util.MiscTools;

import org.jspecify.annotations.NullMarked;

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
@NullMarked
public class ProofBundleSaver extends ProofSaver {

    /**
     * Creates a new ProofBundleSaver.
     *
     * @param proof the proof to save
     * @param saveFile the target filename
     */
    public ProofBundleSaver(Proof proof, Path saveFile) {
        super(proof, saveFile);
    }

    /**
     * Stores the proof bundle in a ZIP archive at the given file path.
     * <p>
     * The init config of the proof to save is always present; the dereference of the (nullable)
     * init config is suppressed with a scoped key.
     */
    @Override
    @SuppressWarnings("nullness:dereference.of.nullable")
    protected void save(Path file) throws IOException {
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
        String proofFileName = MiscTools.toValidFileName(proof.name() + ".proof");

        // save the proof file to the FileRepo (stream is closed by the save method!)
        final var path = Paths.get(proofFileName);
        final Path parent = path.toAbsolutePath().getParent();
        final OutputStream out = repo.createOutputStream(path);
        save(Objects.requireNonNull(parent, "The base path of the proof file must not be null"),
            Objects.requireNonNull(out, "No output stream for the proof file"));

        // save proof bundle with the help of the FileRepo
        ((AbstractFileRepo) repo).saveProof(file);
    }
}
