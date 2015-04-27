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

package de.uka.ilkd.key.control;

import java.io.File;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.ProverTaskListener;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

/**
 * Provides the user interface independent logic to manage multiple proofs. This includes:
 * <ul>
 *    <li>Functionality to load files via {@link #load(Profile, File, List, File, Properties, boolean)}.</li>
 *    <li>Functionality to instantiate new {@link Proof}s via {@link #createProof(InitConfig, ProofOblInput)}.</li>
 *    <li>Functionality to register existing {@link Proof}s in the user interface via {@link #registerProofAggregate(ProofAggregate)}.</li>
 *    <li>Access to the {@link ProofControl} via {@link #getProofControl()}.</li>
 * </ul>
 * @author Martin Hentschel
 */
public interface UserInterfaceControl {
   /**
    * Registers the given {@link ProverTaskListener} which will be informed about all events.
    * @param ptl The {@link ProverTaskListener} to add.
    */
   void addProverTaskListener(ProverTaskListener ptl);
   
   /**
    * Removes the given {@link ProverTaskListener}.
    * @param ptl The {@link ProverTaskListener} to remove.
    */
   void removeProverTaskListener(ProverTaskListener ptl);
   
    /**
     * <p>
     * Opens a java file in this {@link UserInterfaceControl} and returns the instantiated {@link AbstractProblemLoader}
     * which can be used to instantiated proofs programmatically.
     * </p>
     * <p>
     * <b>The loading is performed in the {@link Thread} of the caller!</b>
     * </p>
     * @param profile An optional {@link Profile} to use. If it is {@code null} the default profile {@link KeYMediator#getDefaultProfile()} is used.
     * @param file The java file to open.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param includes Optional includes to consider.
     * @param poPropertiesToForce Some optional {@link Properties} for the PO which extend or overwrite saved PO {@link Properties}.
     * @param forceNewProfileOfNewProofs {@code} true {@link #profileOfNewProofs} will be used as {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file will be used for new proofs.
     * @return The opened {@link AbstractProblemLoader}.
     * @throws ProblemLoaderException Occurred Exception.
     */
    AbstractProblemLoader load(Profile profile, 
                               File file, 
                               List<File> classPaths, 
                               File bootClassPath, 
                               List<File> includes,
                               Properties poPropertiesToForce, 
                               boolean forceNewProfileOfNewProofs) throws ProblemLoaderException;
    
    /**
     * Instantiates a new {@link Proof} in this {@link UserInterfaceControl} for the given
     * {@link ProofOblInput} based on the {@link InitConfig}.
     * @param initConfig The {@link InitConfig} which provides the source code.
     * @param input The description of the {@link Proof} to instantiate.
     * @return The instantiated {@link Proof}.
     * @throws ProofInputException Occurred Exception.
     */
    Proof createProof(InitConfig initConfig, 
                      ProofOblInput input) throws ProofInputException;

    /**
     * Registers an already created {@link ProofAggregate} in this {@link UserInterfaceControl}.
     * @param pa The {@link ProofAggregate} to register.
     */
    void registerProofAggregate(ProofAggregate pa);

    /**
     * Returns the used {@link ProofControl}.
     * @return The used {@link ProofControl}.
     */
    public ProofControl getProofControl();
}