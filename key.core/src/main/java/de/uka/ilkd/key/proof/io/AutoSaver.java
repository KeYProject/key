/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.io;

import java.beans.PropertyChangeListener;
import java.io.File;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.prover.ProverTaskListener;
import de.uka.ilkd.key.prover.TaskFinishedInfo;
import de.uka.ilkd.key.prover.TaskStartedInfo;
import de.uka.ilkd.key.settings.GeneralSettings;
import de.uka.ilkd.key.util.KeYConstants;

import org.key_project.util.java.IOUtil;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;


/**
 * Saves intermediate proof artifacts during strategy execution. An {@link AutoSaver} instance saves
 * periodically and the final proof state if it is closed. The default save interval can be set
 * using the static {@link #init(int, boolean)} method. Before the saver is registered as a
 * listener, <b>a proof must be set</b> with <code>setProof()</code>. AutoSaver writes .key files to
 * a temporary location (i.e., "/tmp" on most Linux machines). These are possibly overwritten on
 * each strategy run. Write errors (e.g., missing permissions) are silently ignored.
 *
 * @author bruns
 */
public class AutoSaver implements ProverTaskListener {
    public static final Logger LOGGER = LoggerFactory.getLogger(AutoSaver.class);

    private static final File TMP_DIR = IOUtil.getTempDirectory();
    private static final String PREFIX = TMP_DIR + File.separator + ".autosave.";

    private Proof proof;
    private final int interval;
    private final boolean saveClosed;

    private static int defaultSaveInterval = 0;
    private static boolean defaultSaveClosedProof = false;

    private static AutoSaver DEFAULT_INSTANCE = null;

    public static final PropertyChangeListener settingsListener =
        e -> {
            assert e.getSource() instanceof GeneralSettings;
            GeneralSettings settings = (GeneralSettings) e.getSource();
            setDefaultValues(settings.autoSavePeriod(), settings.autoSavePeriod() > 0);
        };

    /**
     * Set default values.
     *
     * @param saveInterval the interval (= number of proof steps) to periodically save
     * @param saveClosedProof whether to save the final closed proof
     */
    public static void setDefaultValues(int saveInterval, boolean saveClosedProof) {
        defaultSaveInterval = saveInterval;
        defaultSaveClosedProof = saveClosedProof;
        if (defaultSaveInterval > 0) {
            DEFAULT_INSTANCE = new AutoSaver();
        }
    }

    /**
     * Create a new instance using default values, or null if auto save is disabled by default. The
     * default values can be set through <code>AutoSaver.setDefaultValues()</code>
     */
    public static AutoSaver getDefaultInstance() {
        return DEFAULT_INSTANCE;
    }

    private AutoSaver() {
        this(defaultSaveInterval, defaultSaveClosedProof);
    }

    /**
     * Create a custom instance.
     *
     * @param saveInterval
     * @param saveClosedProof
     */
    public AutoSaver(int saveInterval, boolean saveClosedProof) {
        if (saveInterval <= 0) {
            throw new IllegalArgumentException("Save interval must be positive");
        }
        interval = saveInterval;
        saveClosed = saveClosedProof;
    }

    /**
     * Set the proof to be saved. Call this method <b>before</b> adding this listener to the
     * strategy.
     *
     * @param p proof to save, must not be null
     */
    public void setProof(Proof p) {
        proof = p;
    }

    /**
     * Saves the proof at the end of an interval.
     *
     * @throws IllegalStateException if no proof was set
     */
    @Override
    public void taskProgress(int progress) {
        if (interval == 0) {
            return;
        }
        if (proof == null) {
            return;
        }
        if (progress > 0 && progress % interval == 0) {
            final int quot = progress / interval;
            final String filename = PREFIX + quot + ".key";
            save(filename, proof);
        }
    }

    @Override
    public void taskStarted(TaskStartedInfo info) {
        // currently not used
    }

    @Override
    public void taskFinished(TaskFinishedInfo info) {
        // save proof if closed
        if (saveClosed) {
            if (proof == null) {
                return;
            }
            if (proof.closed()) {
                save(PREFIX + "proof", proof);
            }
        }

        // unset proof
        proof = null;
    }

    private void save(final String filename, final Proof proof) {
        // there may be concurrent changes to the proof... whatever
        final Runnable r = () -> {
            try {
                new ProofSaver(proof, filename, KeYConstants.INTERNAL_VERSION).save();
                LOGGER.info("File saved: {}", filename);
            } catch (Exception e) {
                LOGGER.error("Autosaving file  {} failed.", filename, e);
            }
        };
        (new Thread(null, r, "ProofAutosaver")).start();
    }

}
