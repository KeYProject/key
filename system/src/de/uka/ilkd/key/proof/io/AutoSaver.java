package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Debug;

public final class AutoSaver implements ProverTaskListener {

    private final static String TMP_DIR = System.getProperty("java.io.tmpdir");
    private final static String PREFIX = TMP_DIR+File.separator+".autosave.";
    private static AutoSaver INSTANCE = new AutoSaver(1000); // XXX for testing purposes

    private Proof proof;
    private int interval;

    public static void init ( int saveInterval ) {
        INSTANCE = new AutoSaver(saveInterval);
    }

    public static AutoSaver getInstance() {
        return INSTANCE;
    }

    private AutoSaver (int saveInterval) {
        assert saveInterval >= 0;
        interval = saveInterval;
    }

    public void setProof (Proof p) {
        proof = p;
    }

    @Override
    public void taskProgress(int progress) {
        if (interval == 0) return;
        if (proof == null) throw new IllegalStateException("please set a proof first");
        if (progress > 0 && progress % interval == 0) {
            final int quot = progress/interval;
            final String filename = PREFIX+quot+".key";
            save(filename);
        }
    }

    @Override
    public void taskStarted(String message, int size) {
        // currently not used
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        // unset proof
        proof = null;
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
