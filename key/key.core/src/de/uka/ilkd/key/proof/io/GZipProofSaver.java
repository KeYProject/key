package de.uka.ilkd.key.proof.io;

import de.uka.ilkd.key.proof.Proof;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.util.zip.GZIPOutputStream;

/**
 * Created by tbormer on 12.02.16.
 */
public class GZipProofSaver extends ProofSaver {

    public GZipProofSaver(Proof proof, String fileName, String internalVersion) {
        super(proof, fileName, internalVersion);
    }

    @Override
    protected void save(File file) throws IOException {
        super.save(new GZIPOutputStream(new FileOutputStream(file)));
    }
}
