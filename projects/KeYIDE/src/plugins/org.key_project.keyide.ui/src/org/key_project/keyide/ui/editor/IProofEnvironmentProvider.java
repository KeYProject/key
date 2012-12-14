package org.key_project.keyide.ui.editor;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.CustomConsoleUserInterface;

/**
 * An interface to provide fundamental functions for accessing the {@link KeYEnvironment}.
 * @author Martin Hentschel
 */
public interface IProofEnvironmentProvider {
   
   /**
    * The {@link KeYEnvironment} for this {@link KeYEditor}.
    * @return The {@link KeYEnvironment} for this {@link KeYEditor}.
    */
   public KeYEnvironment<CustomConsoleUserInterface> getKeYEnvironment();

   /**
    * The {@link Proof} for this {@link KeYEditor}.
    * @return The {@link Proof} for this {@link KeYEditor}.
    */
   public Proof getProof();
}
