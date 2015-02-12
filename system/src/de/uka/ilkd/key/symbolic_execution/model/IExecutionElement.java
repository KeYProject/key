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

package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.core.KeYMediator;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.proof.Node;
import de.uka.ilkd.key.proof.NodeInfo;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.init.ProofInputException;

/**
 * Defines the basic methods and properties each element in the 
 * symbolic execution tree model has.
 * @author Martin Hentschel
 */
public interface IExecutionElement {
   /**
    * Returns the {@link ITreeSettings} to use.
    * @return The {@link ITreeSettings} to use.
    */
   public ITreeSettings getSettings();
   
   /**
    * Returns the used {@link KeYMediator} during proof.
    * @return The used {@link KeYMediator} during proof.
    */
   public KeYMediator getMediator();
   
   /**
    * Returns the {@link Services} used in {@link #getProof()}.
    * @return The {@link Services} used in {@link #getProof()}.
    */
   public Services getServices();
   
   /**
    * Returns the {@link Proof} from which the symbolic execution tree was extracted.
    * @return The {@link Proof} from which the symbolic execution tree was extracted.
    */
   public Proof getProof();
   
   /**
    * Returns the {@link Node} in KeY's proof tree which is represented by this execution tree node.
    * @return The {@link Node} in KeY's proof tree which is represented by this execution tree node.
    */
   public Node getProofNode();
   
   /**
    * Returns the {@link PosInOccurrence} of the modality of interest including updates.
    * @return The {@link PosInOccurrence} of the modality of interest including updates.
    */
   public PosInOccurrence getModalityPIO();
   
   /**
    * Returns the {@link NodeInfo} of {@link #getProofNode()}.
    * @return The {@link NodeInfo} of {@link #getProofNode()}.
    */
   public NodeInfo getProofNodeInfo();
   
   /**
    * Returns a human readable name which describes this element.
    * @return The human readable name which describes this element.
    * @throws ProofInputException Occurred Exception.
    */
   public String getName() throws ProofInputException;
   
   /**
    * Returns a human readable element type name.
    * @return The human readable element type.
    */
   public String getElementType();
   
   /**
    * Checks if the proof is disposed.
    * @return {@code true} proof is disposed, {@code false} proof is not disposed and still valid.
    */
   public boolean isDisposed();
}