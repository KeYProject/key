package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Debug;

/**
 * Saves intermediate proof artifacts during strategy execution.
 * The singleton saver is obtained through <code>getInstance()</code>,
 * it saves periodically and the final proof state if it is closed.
 * The save interval can be set using the static <code>init()</code> method.
 * Before the saver is registered as a listener, <b>a proof must be set</b> with <code>setProof()</code>.
 * AutoSaver writes .key files to a temporary location (i.e., "/tmp" on most Linux machines).
 * These are possibly overwritten on each strategy run.
 * Write errors (e.g., missing permissions) are silently ignored.
 * @author bruns
 */
public final class AutoSaver implements ProverTaskListener {

    private final static String TMP_DIR = System.getProperty("java.io.tmpdir");
    private final static String PREFIX = TMP_DIR+File.separator+".autosave.";
    private static AutoSaver INSTANCE = new AutoSaver(0, false);

    private Proof proof;
    private final int interval;
    private final boolean saveClosed;

    /**
     * Initialize the singleton instance.
     * @param saveInterval the interval (= number of proof steps) to periodically save
     * @param saveClosedProof whether to save the final closed proof
     */
    public static void init ( int saveInterval, boolean saveClosedProof ) {
        INSTANCE = new AutoSaver(saveInterval, saveClosedProof);
    }

    public static AutoSaver getInstance() {
        return INSTANCE;
    }

    private AutoSaver (int saveInterval, boolean saveClosedProof) {
        assert saveInterval >= 0;
        interval = saveInterval;
        saveClosed = saveClosedProof;
    }

    /**
     * Set the proof to be saved.
     * Call this method <b>before</b> adding this listener to the strategy.
     * @param p proof to save, must not be null
     */
    public void setProof (Proof p) {
        if (p == null) throw new IllegalArgumentException("proof must not be null");
        proof = p;
    }

    /**
     * Saves the proof at the end of an interval.
     * @throws IllegalStateException if no proof was set
     */
    @Override
    public void taskProgress(int progress) {
        if (interval == 0) return;
        if (proof == null) throw new IllegalStateException("please set a proof first");
        if (progress > 0 && progress % interval == 0) {
            final int quot = progress/interval;
            final String filename = PREFIX+quot+".key";
            save(filename,proof);
        }
    }

    @Override
    public void taskStarted(String message, int size) {
        // currently not used
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        // save proof if closed
        if (saveClosed) {
            if (proof == null) throw new IllegalStateException("please set a proof first");
            if (proof.closed()) {
                save(PREFIX+"proof",proof);
            }
        }

        // unset proof
        proof = null;
    }

    private void save(final String filename, final Proof proof) {
        final Runnable r = new Runnable() {

            // there may be concurrent changes to the proof... whatever
            public void run() {
                try {
                    new ProofSaver(proof, filename, de.uka.ilkd.key.gui.Main.INTERNAL_VERSION).save();
                    Debug.out("File saved: "+filename);
                } catch (IOException e) {
                    Debug.out("Autosaving file "+filename+" failed.",e);
                } catch (Exception x) {
                    // really should not happen, but catching prevents worse
                    x.printStackTrace();
                }
            }
        };
        (new Thread(null,r,"ProofAutosaver")).run();
    }

}
