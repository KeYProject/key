/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.io;

import java.util.Properties;

import org.key_project.rusty.proof.ProofAggregate;
import org.key_project.rusty.proof.init.InitConfig;
import org.key_project.rusty.proof.init.ProofOblInput;
import org.key_project.rusty.proof.io.AbstractProblemLoader.ReplayResult;
import org.key_project.util.collection.ImmutableSet;

/**
 * Allows to observe and control the loading performed by an {@link AbstractProblemLoader}.
 *
 * @author Martin Hentschel
 */
public interface ProblemLoaderControl {
    /**
     * The loading has started.
     *
     * @param loader The source {@link AbstractProblemLoader}.
     */
    void loadingStarted(AbstractProblemLoader loader);

    /**
     * The loading has stopped.
     *
     * @param loader The source {@link AbstractProblemLoader}.
     * @param poContainer The loaded {@link LoadedPOContainer}.
     * @param proofList The created {@link ProofAggregate}.
     * @param result The occurred {@link ReplayResult}.
     * @throws ProblemLoaderException Occurred Exception.
     */
    void loadingFinished(AbstractProblemLoader loader, LoadedPOContainer poContainer,
            ProofAggregate proofList, ReplayResult result) throws ProblemLoaderException;

    /**
     * This method is called if no {@link LoadedPOContainer} was created via
     * {@link AbstractProblemLoader#createProofObligationContainer()} and can be overwritten for
     * instance to open the proof management dialog as done by {@link AbstractProblemLoader}.
     *
     * @return true if the proof obligation was selected, and false if action was aborted
     */
    boolean selectProofObligation(InitConfig initConfig);

    /**
     * Report the occurred warnings.
     *
     * @param warnings The occurred warnings.
     */
    void reportWarnings(ImmutableSet<String> warnings);

    /**
     * The class stored in a {@link Properties} instance via key must provide the static method with
     * the following signature:
     * {@code public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws IOException}
     * This method is called by the {@link AbstractProblemLoader} to
     * recreate a proof obligation. This class
     * defines the result of this method which is the created proof obligation and its proof number.
     *
     * @author Martin Hentschel
     */
    class LoadedPOContainer {
        /**
         * The created {@link ProofOblInput}.
         */
        private final ProofOblInput proofOblInput;

        /**
         * The proof number which is {@code 0} by default.
         */
        private final int proofNum;

        /**
         * Constructor.
         *
         * @param proofOblInput The created {@link ProofOblInput}.
         */
        public LoadedPOContainer(ProofOblInput proofOblInput) {
            this(proofOblInput, 0);
        }

        /**
         * Constructor.
         *
         * @param proofOblInput The created {@link ProofOblInput}.
         * @param proofNum The proof number which is {@code 0} by default.
         */
        public LoadedPOContainer(ProofOblInput proofOblInput, int proofNum) {
            super();
            this.proofOblInput = proofOblInput;
            this.proofNum = proofNum;
        }

        /**
         * Returns the created {@link ProofOblInput}.
         *
         * @return The created {@link ProofOblInput}.
         */
        public ProofOblInput getProofOblInput() {
            return proofOblInput;
        }

        /**
         * Returns the proof number which is {@code 0} by default.
         *
         * @return The proof number which is {@code 0} by default.
         */
        public int getProofNum() {
            return proofNum;
        }
    }
}
