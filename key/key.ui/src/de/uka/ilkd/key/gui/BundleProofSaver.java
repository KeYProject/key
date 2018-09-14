package de.uka.ilkd.key.gui;

import java.io.File;
import java.io.FileOutputStream;
import java.io.IOException;
import java.nio.file.Files;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.proof.io.consistency.FileRepo;

public class BundleProofSaver extends ProofSaver {

    public BundleProofSaver(Proof proof, String fileName, String internalVersion) {
        super(proof, fileName, internalVersion);
    }

    @Override
    protected void save(File file) throws IOException {
        // get the FileRepo from the InitConfig of the Proof
        FileRepo repo = proof.getInitConfig().getFileRepo();
        
        // save proof file to stream/file
        // create a temporary file in the base dir of the proof -> TODO: may fail?!
        String tmpFileName = file.getName().replaceFirst("(.*).zproof", "$1.proof");
        File tmp = repo.getBaseDir().resolve(tmpFileName).toFile();
        super.save(new FileOutputStream(tmp));
        
        /*
        byte[] chars = new byte[1024];
        ByteArrayOutputStream baos = new ByteArrayOutputStream(1024);
        super.save(baos);
        chars = baos.toByteArray();
        System.out.println(chars.toString());
        */
        
        // load tmp proof file into FileRepo (and instantly release the resources)
        repo.getFile(tmp.toPath()).close();

        // save proof bundle with the help of the Repo
        repo.saveProof(file.toPath(), proof);
        
        // delete tmp file
        Files.delete(tmp.toPath());
    }
}
