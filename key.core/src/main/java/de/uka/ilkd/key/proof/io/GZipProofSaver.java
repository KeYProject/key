/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.zip.GZIPOutputStream;

import de.uka.ilkd.key.proof.Proof;

/**
 * This proof saver derivative wraps its generated output stream into a {@link GZIPOutputStream}
 * thus compressing proof files.
 *
 * @author tbormer on 12.02.16.
 */
public class GZipProofSaver extends ProofSaver {

    /**
     * Instantiates a new proof saver.
     *
     * @param proof the non-<code>null</code> proof to save
     * @param fileName the name of the file to write to
     * @param internalVersion the internal version
     */
    public GZipProofSaver(Proof proof, String fileName, String internalVersion) {
        super(proof, fileName, internalVersion);
    }

    /**
     * {@inheritDoc}
     * <p>
     * This subclass wraps the file stream into a {@link GZIPOutputStream}.
     */
    @Override
    protected void save(Path file) throws IOException {
        try (var out = new GZIPOutputStream(Files.newOutputStream(file))) {
            save(out);
        }
    }
}
