package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Debug;

public class AutoSaver implements ProverTaskListener {

    private final static String TMP_DIR = System.getProperty("java.io.tmpdir");
    private final static String PREFIX = TMP_DIR+File.separator+".autosave.";

    private Proof proof;
    private final int interval;
    private final String basename;

    public AutoSaver (String basename, int saveInterval) {
        assert basename != null;
        assert saveInterval > 0;
        interval = saveInterval;
        this.basename = basename;
    }

    public void setProof (Proof p) {
        proof = p;
    }

    @Override
    public void taskProgress(int progress) {
        if (proof == null) throw new IllegalStateException("please set a proof first");
        if (progress > 0 && progress % interval == 0) {
            final int quot = progress/interval;
            final String filename = PREFIX+basename+"."+quot+".key";
            save(filename);
        }
    }

    @Override
    public void taskStarted(String message, int size) {
        // currently not used
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        // currently not used
    }

    private void save(String filename) {
        try {
            new ProofSaver(proof, filename, de.uka.ilkd.key.gui.Main.INTERNAL_VERSION).save();
            System.out.println("File saved: "+filename); // XXX
        } catch (IOException e) {
            Debug.out("Autosave failed.",e);
            System.out.println("File save failed: "+filename); // XXX
        }
    }

}
