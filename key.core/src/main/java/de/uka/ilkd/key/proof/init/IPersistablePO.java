/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.proof.init;

import java.io.IOException;
import java.util.Properties;

import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.proof.io.ProofSaver;
import de.uka.ilkd.key.settings.Configuration;

/**
 * <p>
 * This interface extends the standard proof obligation ({@link ProofOblInput}) with functionality
 * to define the individual parameters which are required for loading and saving {@code *.proof}
 * files.
 * </p>
 * <p>
 * During save process the {@link ProofSaver} calls method {@link #createLoaderConfig()}.
 * This proof obligation has to store all information in the given {@link Properties} which are
 * required to reconstruct it. The class ({@link Object#getClass()}) of this class must be stored in
 * the
 * {@link Properties} with key {@link #PROPERTY_CLASS}.
 * </p>
 * <p>
 * During load process the {@link de.uka.ilkd.key.proof.io.AbstractProblemLoader} tries to execute a
 * static method on the class
 * defined via {@link Properties} key {@link #PROPERTY_CLASS} with the following signature:
 * {@code public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws IOException}
 * The returned {@link LoadedPOContainer} contains the instantiated {@link ProofOblInput} together
 * with the proof index.
 * </p>
 *
 * @author Martin Hentschel
 * @see ProofSaver
 * @see de.uka.ilkd.key.proof.io.AbstractProblemLoader
 */
public interface IPersistablePO extends ProofOblInput {
    /**
     * The key used to store {@link Object#getClass()}.
     */
    String PROPERTY_CLASS = "class";

    /**
     * The key used to store {@link ProofOblInput#name()}.
     */
    String PROPERTY_NAME = "name";

    /**
     * The key used to store the file name under which a PO is loaded. This key is set during
     * loading by the loader and needs not be saved.
     */
    String PROPERTY_FILENAME = "#key.filename";

    /**
     * The key used to store {@link AbstractOperationPO#isAddSymbolicExecutionLabel()}.
     */
    String PROPERTY_ADD_SYMBOLIC_EXECUTION_LABEL = "addSymbolicExecutionLabel";

    /**
     * The key used to store {@link AbstractOperationPO#isAddUninterpretedPredicate()}.
     */
    String PROPERTY_ADD_UNINTERPRETED_PREDICATE = "addUninterpretedPredicate";

    /**
     * This method is called by a {@link ProofSaver} to store the proof specific settings in the
     * given {@link Properties}. The stored settings have to contain all information required to
     * instantiate the proof obligation again and this instance should create the same
     * {@link Sequent} (if code and specifications are unchanged).
     *
     * @return
     * @throws IOException Occurred Exception.
     */
    Configuration createLoaderConfig() throws IOException;

    /**
     * The class stored in a {@link Properties} instance via key must provide the static method with
     * the following signature:
     * {@code public static LoadedPOContainer loadFrom(InitConfig initConfig, Properties properties) throws IOException}
     * This method is called by the {@link de.uka.ilkd.key.proof.io.AbstractProblemLoader} to
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
