package org.key_project.sed.key.evaluation.server.random;

import java.util.HashMap;
import java.util.Map;

/**
 * Manages the available {@link IRandomCompletion} implementations.
 * @author Martin Hentschel
 */
public final class RandomCompletionManager {
   /**
    * Contains all available {@link IRandomCompletion}s.
    */
   private final static Map<String, IRandomCompletion> randomCompletions = new HashMap<String, IRandomCompletion>();
   
   /**
    * Forbid instances.
    */
   private RandomCompletionManager() {
   }

   /**
    * Register an {@link IRandomCompletion} under the given name.
    * @param name The name of the random completion.
    * @param completion The {@link IRandomCompletion} instance.
    */
   public static void registerRandomCompletion(String name, IRandomCompletion completion) {
      if (name != null && completion != null) {
         randomCompletions.put(name, completion);
      }
   }
   
   /**
    * Creates the {@link IRandomCompletion} with the given name.
    * @param name The name of the {@link IRandomCompletion} to create.
    * @return The created {@link IRandomCompletion} or {@code null} if the name is unknown.
    */
   public static IRandomCompletion createRandomCompletion(String name) {
      if (name != null) {
         return randomCompletions.get(name);
      }
      else {
         return null;
      }
   }
}
