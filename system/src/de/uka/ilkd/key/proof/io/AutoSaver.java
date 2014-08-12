// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.proof.io;

import java.io.File;
import java.io.IOException;

import de.uka.ilkd.key.gui.ProverTaskListener;
import de.uka.ilkd.key.gui.TaskFinishedInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.util.Debug;

/**
 * Saves intermediate proof artifacts during strategy execution.
 * An {@link AutoSaver} instance saves periodically and the final proof state if it is closed.
 * The default save interval can be set using the static {@link #init(int, boolean)} method.
 * Before the saver is registered as a listener, <b>a proof must be set</b> with <code>setProof()</code>.
 * AutoSaver writes .key files to a temporary location (i.e., "/tmp" on most Linux machines).
 * These are possibly overwritten on each strategy run.
 * Write errors (e.g., missing permissions) are silently ignored.
 * @author bruns
 */
public class AutoSaver implements ProverTaskListener {

    private final static String TMP_DIR = System.getProperty("java.io.tmpdir");
    private final static String PREFIX = TMP_DIR+File.separator+".autosave.";
    
    private Proof proof;
    private final int interval;
    private final boolean saveClosed;

    private static int defaultSaveInterval = 0;
    private static boolean defaultSaveClosedProof = false;
    
    /**
     * Set default values.
     * @param saveInterval the interval (= number of proof steps) to periodically save
     * @param saveClosedProof whether to save the final closed proof
     */
    public static void setDefaultValues ( int saveInterval, boolean saveClosedProof ) {
       defaultSaveInterval = saveInterval;
       defaultSaveClosedProof = saveClosedProof;
    }
    
    /**
     * Create a new instance using default values, 
     * or null if auto save is disabled by default.
     * The default values can be set through <code>AutoSaver.setDefaultValues()</code>
     */
    public static AutoSaver getDefaultInstance() {
        return defaultSaveInterval > 0 || defaultSaveClosedProof?
                        new AutoSaver(): null;
    }

    private AutoSaver () {
       this(defaultSaveInterval, defaultSaveClosedProof);
    }
    
    /**
     * Create a custom instance.
     * @param saveInterval
     * @param saveClosedProof
     */
    public AutoSaver (int saveInterval, boolean saveClosedProof) {
        if (saveInterval <= 0)
            throw new IllegalArgumentException("Save interval must be positive");
        interval = saveInterval;
        saveClosed = saveClosedProof;
    }

    /**
     * Set the proof to be saved.
     * Call this method <b>before</b> adding this listener to the strategy.
     * @param p proof to save, must not be null
     */
    public void setProof (Proof p) {
        proof = p;
    }

    /**
     * Saves the proof at the end of an interval.
     * @throws IllegalStateException if no proof was set
     */
    @Override
    public void taskProgress(int progress) {
        if (interval == 0) return;
        if (proof == null) return;
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
            if (proof == null) return;
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
        (new Thread(null,r,"ProofAutosaver")).start(); 
    }

}