package org.key_project.keyide.ui.editor;

import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;

public interface IProofEnvironmentProvider {
   public KeYEnvironment<?> getKeYEnvironment();

      public Proof getProof();
}
