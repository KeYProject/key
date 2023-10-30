/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.io.IOException;
import java.io.InputStream;
import java.io.OutputStream;
import java.nio.file.Files;
import java.nio.file.Path;

import de.uka.ilkd.key.control.DefaultUserInterfaceControl;
import de.uka.ilkd.key.control.KeYEnvironment;

import org.junit.jupiter.api.Test;

public class TestZipProofSaving {

    @Test
    public void testZip() throws Exception {

        Path file = Files.createTempFile("keyZipTest", ".key");
        Path fileTarget = Files.createTempFile("keyZipTest", ".proof.gz");
        drain(getClass().getResourceAsStream("keyZipTest.key"), Files.newOutputStream(file));
        proveAndSaveZip(file, fileTarget);

        loadZip(fileTarget);
    }

    private void loadZip(Path fileTarget) throws Exception {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(fileTarget.toFile());
        env.getProofControl().startAndWaitForAutoMode(env.getLoadedProof());
    }

    private void proveAndSaveZip(Path file, Path fileTarget)
            throws ProblemLoaderException, IOException {
        KeYEnvironment<DefaultUserInterfaceControl> env = KeYEnvironment.load(file.toFile());
        env.getProofControl().startAndWaitForAutoMode(env.getLoadedProof());
        GZipProofSaver proofSaver =
            new GZipProofSaver(env.getLoadedProof(), fileTarget.toString(), "n/a");
        proofSaver.save();
    }

    private void drain(InputStream is, OutputStream os) throws IOException {
        try {
            byte[] buffer = new byte[4096];
            int read = is.read(buffer);
            while (read >= 0) {
                os.write(buffer, 0, read);
                read = is.read(buffer);
            }
        } finally {
            if (is != null) {
                is.close();
            }
            if (os != null) {
                os.close();
            }
        }
    }

}
