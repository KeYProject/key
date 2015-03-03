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

package de.uka.ilkd.key.ui;

import java.io.File;
import java.util.List;
import java.util.Properties;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.InitConfig;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.ProofOblInput;
import de.uka.ilkd.key.proof.io.AbstractProblemLoader;
import de.uka.ilkd.key.proof.io.ProblemLoaderException;

public interface UserInterface {  
    /**
     * <p>
     * Opens a java file in this {@link UserInterface} and returns the instantiated {@link AbstractProblemLoader}
     * which can be used to instantiated proofs programmatically.
     * </p>
     * <p>
     * <b>The loading is performed in the {@link Thread} of the caller!</b>
     * </p>
     * @param profile An optional {@link Profile} to use. If it is {@code null} the default profile {@link KeYMediator#getDefaultProfile()} is used.
     * @param file The java file to open.
     * @param classPaths The class path entries to use.
     * @param bootClassPath The boot class path to use.
     * @param poPropertiesToForce Some optional {@link Properties} for the PO which extend or overwrite saved PO {@link Properties}.
     * @param forceNewProfileOfNewProofs {@code} true {@link #profileOfNewProofs} will be used as {@link Profile} of new proofs, {@code false} {@link Profile} specified by problem file will be used for new proofs.
     * @return The opened {@link AbstractProblemLoader}.
     * @throws ProblemLoaderException Occurred Exception.
     */
    AbstractProblemLoader load(Profile profile, 
                               File file, 
                               List<File> classPaths, 
                               File bootClassPath, 
                               Properties poPropertiesToForce, 
                               boolean forceNewProfileOfNewProofs) throws ProblemLoaderException;
    
    /**
     * Instantiates a new {@link Proof} in this {@link UserInterface} for the given
     * {@link ProofOblInput} based on the {@link InitConfig}.
     * @param initConfig The {@link InitConfig} which provides the source code.
     * @param input The description of the {@link Proof} to instantiate.
     * @return The instantiated {@link Proof}.
     * @throws ProofInputException Occurred Exception.
     */
    Proof createProof(InitConfig initConfig, 
                      ProofOblInput input) throws ProofInputException;

    /**
     * Returns the used {@link ProofControl}.
     * @return The used {@link ProofControl}.
     */
    public ProofControl getProofControl();
    
    /**
     * Removes the given {@link Proof} from this {@link UserInterface}.
     * @param proof The {@link Proof} to remove.
     */
    void removeProof(Proof proof);
}