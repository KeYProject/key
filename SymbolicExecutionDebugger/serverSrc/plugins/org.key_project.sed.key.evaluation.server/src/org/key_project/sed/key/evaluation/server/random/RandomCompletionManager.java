package org.key_project.sed.key.evaluation.server.random;

import org.key_project.sed.key.evaluation.model.definition.UnderstandingProofAttemptsEvaluation;

/**
 * Manages the available {@link IRandomCompletion} implementations.
 * @author Martin Hentschel
 */
public final class RandomCompletionManager {
   /**
    * Forbid instances.
    */
   private RandomCompletionManager() {
   }
   
   /**
    * Creates the {@link IRandomCompletion} with the given name.
    * @param name The name of the {@link IRandomCompletion} to create.
    * @return The created {@link IRandomCompletion} or {@code null} if the name is unknown.
    */
   public static IRandomCompletion createRandomCompletion(String name) {
      if (UnderstandingProofAttemptsEvaluation.RANDOM_COMPUTER_NAME.equals(name)) {
         return new UnderstandingProofAttemptsRandomFormOrderComputer();
      }
      else {
         return null;
      }
   }
}
