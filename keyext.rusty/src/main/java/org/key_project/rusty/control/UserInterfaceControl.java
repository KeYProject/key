/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.control;

import java.io.File;
import java.util.List;
import java.util.Properties;
import java.util.function.Consumer;

import org.key_project.rusty.proof.Proof;
import org.key_project.rusty.proof.ProofAggregate;
import org.key_project.rusty.proof.init.InitConfig;
import org.key_project.rusty.proof.init.Profile;
import org.key_project.rusty.proof.init.ProofInputException;
import org.key_project.rusty.proof.init.ProofOblInput;
import org.key_project.rusty.proof.io.AbstractProblemLoader;
import org.key_project.rusty.proof.io.ProblemLoaderException;

/**
 * Provides the user interface independent logic to manage multiple proofs. This includes:
 * <ul>
 * <li>Functionality to load files via
 * {@link #load(Profile, File, List, File, List, Properties, boolean, Consumer)}.</li>
 * <li>Functionality to instantiate new {@link Proof}s via
 * {@link #createProof(InitConfig, ProofOblInput)}.</li>
 * <li>Functionality to register existing {@link Proof}s in the user interface via
 * {@link #registerProofAggregate(ProofAggregate)}.</li>
 * </ul>
 *
 * @author Martin Hentschel
 */
public interface UserInterfaceControl {
    /**
     * <p>
     * Opens a java file in this {@link UserInterfaceControl} and returns the instantiated
     * {@link AbstractProblemLoader} which can be used to instantiated proofs programmatically.
     * </p>
     * <p>
     * <b>The loading is performed in the {@link Thread} of the caller!</b>
     * </p>
     *
     * @param profile An optional {@link Profile} to use. If it is {@code null} the default profile
     *        {@link AbstractProfile#getDefaultProfile()} is used.
     * @param file The java file to open.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param includes Optional includes to consider.
     * @param poPropertiesToForce Some optional {@link Properties} for the PO which extend or
     *        overwrite saved PO {@link Properties}.
     * @param forceNewProfileOfNewProofs {@code} true
     *        {@code AbstractProblemLoader.profileOfNewProofs} will be used as {@link Profile} of
     *        new proofs, {@code false} {@link Profile} specified by problem file will be used for
     *        new proofs.
     * @param callbackProofLoaded receives the proof after it is loaded, but before it is replayed
     * @return The opened {@link AbstractProblemLoader}.
     * @throws ProblemLoaderException Occurred Exception.
     */
    AbstractProblemLoader load(Profile profile, File file, List<File> classPaths,
            File bootClassPath, List<File> includes, Properties poPropertiesToForce,
            boolean forceNewProfileOfNewProofs,
            Consumer<Proof> callbackProofLoaded) throws ProblemLoaderException;

    /**
     * Instantiates a new {@link Proof} in this {@link UserInterfaceControl} for the given
     * {@link ProofOblInput} based on the {@link InitConfig}.
     *
     * @param initConfig The {@link InitConfig} which provides the source code.
     * @param input The description of the {@link Proof} to instantiate.
     * @return The instantiated {@link Proof}.
     * @throws ProofInputException Occurred Exception.
     */
    Proof createProof(InitConfig initConfig, ProofOblInput input) throws ProofInputException;

    /**
     * Registers an already created {@link ProofAggregate} in this {@link UserInterfaceControl}.
     *
     * @param pa The {@link ProofAggregate} to register.
     */
    void registerProofAggregate(ProofAggregate pa);


}
