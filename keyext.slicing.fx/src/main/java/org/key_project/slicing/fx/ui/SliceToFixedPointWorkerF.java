/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2,
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.slicing.fx.ui;

import java.nio.file.Path;
import java.util.function.Supplier;

import javafx.concurrent.Task;

import de.uka.ilkd.key.proof.Proof;

import org.key_project.slicing.analysis.AnalysisResults;
import org.key_project.util.javafx.FxUtil;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Worker to analyze and slice a proof, FX port of
 * {@code org.key_project.slicing.ui.SliceToFixedPointWorker} (a SwingWorker): the background
 * task analyzes the proof (via the wrapped analyze callback of the dialog) and either reports
 * "no more slicing possible" (the fixed point is reached, {@code doneCallback} runs) or
 * disposes the previous intermediate slice and triggers the slice button on the FX thread.
 *
 * @author Alexander Weigl (FX port)
 * @author Arne Keller (Swing original)
 */
@NullMarked
final class SliceToFixedPointWorkerF {

    private static final Logger LOGGER = LoggerFactory.getLogger(SliceToFixedPointWorkerF.class);

    /** The proof to analyze and slice. */
    private final Proof proof;
    /** The proof to dispose after successfully completing analysis + slicing. */
    private final @Nullable Proof proofToDispose;
    /**
     * Function that provides the analysis results of the {@link #proof} (the dialog's wrapped
     * analyze callback).
     */
    private final Supplier<@Nullable AnalysisResults> analyzeCallback;
    /** Callback that starts slicing the {@link #proof} (invoked on the FX thread). */
    private final Runnable sliceCallback;
    /** Callback called if the proof cannot be sliced further (invoked on the FX thread). */
    private final Runnable doneCallback;

    /**
     * Construct a new worker (Swing {@code SliceToFixedPointWorker} constructor).
     *
     * @param proofToSlice the proof to slice
     * @param proofToDispose the proof to dispose after successfully analyzing and slicing the
     *        current proof
     * @param analyzeCallback callback that provides the analysis results
     * @param sliceCallback callback to slice the proof
     * @param doneCallback called if the proof can not be sliced further
     */
    SliceToFixedPointWorkerF(Proof proofToSlice, @Nullable Proof proofToDispose,
            Supplier<@Nullable AnalysisResults> analyzeCallback, Runnable sliceCallback,
            Runnable doneCallback) {
        this.proof = proofToSlice;
        this.proofToDispose = proofToDispose;
        this.analyzeCallback = analyzeCallback;
        this.sliceCallback = sliceCallback;
        this.doneCallback = doneCallback;
    }

    /**
     * Start the background analysis (Swing {@code SliceToFixedPointWorker.execute} +
     * {@code doInBackground}).
     */
    void execute() {
        Task<Void> task = new Task<>() {
            @Override
            protected Void call() {
                LOGGER.info("analyzing proof {} (ID: {})", proof.name(),
                    System.identityHashCode(proof));
                @Nullable AnalysisResults results;
                try {
                    results = analyzeCallback.get();
                } catch (Exception e) {
                    LOGGER.error("failed to analyze proof", e);
                    results = null;
                }
                if (results == null || !results.indicateSlicingPotential()) {
                    // fixed point reached: no more steps can be removed
                    LOGGER.info("analysis: no more slicing possible");
                    FxUtil.runLater(doneCallback);
                } else {
                    if (proofToDispose != null) {
                        LOGGER.info("disposing intermediate proof slice {} (ID: {})",
                            proofToDispose.name(), System.identityHashCode(proofToDispose));
                        proofToDispose.dispose();
                    }
                    LOGGER.info("slicing proof {} (ID: {})", proof.name(),
                        System.identityHashCode(proof));
                    FxUtil.runLater(sliceCallback);
                }
                return null;
            }
        };
        Thread thread = new Thread(task, "SliceToFixedPoint");
        thread.setDaemon(true);
        thread.start();
    }

    /** @return the proof sliced by this worker (Swing {@code getSlicedProof}) */
    Proof getSlicedProof() {
        return proof;
    }
}
