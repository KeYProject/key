/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.slicing.ui;

import java.util.function.Function;
import javax.swing.*;

import de.uka.ilkd.key.proof.Proof;

import org.key_project.slicing.analysis.AnalysisResults;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Worker to analyze and slice a proof.
 *
 * @author Arne Keller
 */
final class SliceToFixedPointWorker extends SwingWorker<Void, Void> {
    /**
     * Logger.
     */
    private static final Logger LOGGER = LoggerFactory.getLogger(SliceToFixedPointWorker.class);

    /**
     * The proof to analyze and slice.
     */
    private final Proof proof;
    /**
     * The proof to dispose after successfully completing analysis + slicing.
     */
    private Proof proofToDispose;
    /**
     * Function that provides analysis results for the {@link #proof}.
     */
    private final Function<Void, AnalysisResults> analyzeButton;
    /**
     * Callback that starts slicing the {@link #proof}.
     */
    private final Runnable sliceButton;
    /**
     * Callback called if proof cannot be sliced any further.
     */
    private final Runnable doneCallback;

    /**
     * Construct a new worker.
     *
     * @param proofToSlice the proof to slice
     * @param proofToDispose the proof to dispose after successfully analyzing and slicing the
     *        current proof
     * @param analyzeButton callback that provides analysis results
     * @param sliceButton callback to slice the proof
     * @param doneCallback called if the proof can not be sliced further
     */
    public SliceToFixedPointWorker(Proof proofToSlice,
            Proof proofToDispose,
            Function<Void, AnalysisResults> analyzeButton,
            Runnable sliceButton,
            Runnable doneCallback) {
        this.proof = proofToSlice;
        this.proofToDispose = proofToDispose;
        this.analyzeButton = analyzeButton;
        this.sliceButton = sliceButton;
        this.doneCallback = doneCallback;
    }

    @Override
    protected Void doInBackground() {
        LOGGER.info("analyzing proof {} (ID: {})", proof.name(), System.identityHashCode(proof));
        if (isCancelled()) {
            doneCallback.run();
            return null;
        }
        AnalysisResults results = analyzeButton.apply(null);
        if (!results.indicateSlicingPotential()) {
            LOGGER.info("analysis: no more slicing possible");
            doneCallback.run();
        } else {
            if (proofToDispose != null) {
                LOGGER.info("disposing intermediate proof slice {} (ID: {})", proofToDispose.name(),
                    System.identityHashCode(proofToDispose));
                proofToDispose.dispose();
            }
            proofToDispose = proof;
            LOGGER.info("slicing proof {} (ID: {})", proof.name(), System.identityHashCode(proof));
            SwingUtilities.invokeLater(sliceButton);
        }
        return null;
    }

    @Override
    protected void done() {

    }

    /**
     * @return the proof sliced by this worker
     */
    public Proof getSlicedProof() {
        return proof;
    }
}
