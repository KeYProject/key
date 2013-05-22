package org.key_project.key4eclipse.starter.core.util.event;

import java.util.EventObject;

import org.key_project.key4eclipse.starter.core.util.IProofProvider;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * An event thrown by an {@link IProofProvider} observed via an {@link IProofProviderListener}.
 * @author Martin Hentschel
 */
public class ProofProviderEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 4207369123089010804L;

   /**
    * The current {@link Proof}s.
    */
   private Proof[] currentProofs;
   
   /**
    * The current {@link Proof}, e.g. the first of {@link #currentProofs}.
    */
   private Proof currentProof;
   
   /**
    * The optional {@link UserInterface} in which {@link #currentProofs} lives.
    */
   private UserInterface userInterface;
   
   /**
    * The optional {@link KeYEnvironment} in which {@link #currentProofs} lives.
    */
   private KeYEnvironment<?> environment;
   
   /**
    * Constructor.
    * @param source The source {@link IProofProvider} which throws this event.
    * @param currentProofs The current {@link Proof}s.
    * @param currentProof The current {@link Proof}, e.g. the first one of {@link #getCurrentProofs()}.
    * @param userInterface The optional {@link UserInterface} in which {@link #getCurrentProofs()} lives.
    * @param environment The optional {@link KeYEnvironment} in which {@link #getCurrentProofs()} lives.
    */
   public ProofProviderEvent(IProofProvider source, 
                             Proof[] currentProofs,
                             Proof currentProof,
                             UserInterface userInterface,
                             KeYEnvironment<?> environment) {
      super(source);
      this.currentProofs = currentProofs;
      this.currentProof = currentProof;
      this.userInterface = userInterface;
      this.environment = environment;
   }

   /**
    * Returns the current {@link Proof}s.
    * @return The current {@link Proof}s.
    */
   public Proof[] getCurrentProofs() {
      return currentProofs;
   }

   /**
    * Returns the current {@link Proof}, e.g. the first one of {@link #getCurrentProofs()}.
    * @return The current {@link Proof}.
    */
   public Proof getCurrentProof() {
      return currentProof;
   }

   /**
    * Returns the optional {@link UserInterface} in which {@link #getCurrentProofs()} lives.
    * @return The {@link UserInterface} in which {@link #getCurrentProofs()} lives or {@code null} if not available.
    */
   public UserInterface getUserInterface() {
      return userInterface;
   }

   /**
    * Returns the optional  {@link KeYEnvironment} in which {@link #getCurrentProofs()} lives.
    * @return The {@link KeYEnvironment} in which {@link #getCurrentProofs()} lives or {@code null} if not available.
    */
   public KeYEnvironment<?> getEnvironment() {
      return environment;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public IProofProvider getSource() {
      return (IProofProvider)super.getSource();
   }
}
