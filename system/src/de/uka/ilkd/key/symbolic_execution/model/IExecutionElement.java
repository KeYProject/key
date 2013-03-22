package de.uka.ilkd.key.symbolic_execution.model;

import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.java.Services;
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
