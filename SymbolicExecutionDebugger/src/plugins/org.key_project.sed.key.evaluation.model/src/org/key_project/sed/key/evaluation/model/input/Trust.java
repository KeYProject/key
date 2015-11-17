package org.key_project.sed.key.evaluation.model.input;

/**
 * The different kinds of trust in the correctness of a given answer.
 * @author Martin Hentschel
 */
public enum Trust {
   /**
    * Sure: My answer is correct!
    */
   SURE {
      /**
       * {@inheritDoc}
       */
      @Override
      public String getName() {
         return "sure";
      }
   },
   
   /**
    * Educated Guess: As far as I understood the content, my answer should be correct!
    */
   EDUCATED_GUESS {
      /**
       * {@inheritDoc}
       */
      @Override
      public String getName() {
         return "educated guess";
      }
   },
   
   /**
    * Unsure: I tried my best, but I don't believe that my answer is correct.
    */
   UNSURE {
      /**
       * {@inheritDoc}
       */
      @Override
      public String getName() {
         return "unsure";
      }
   };
   
   /**
    * Returns the human readable trust name.
    * @return The human readable trust name.
    */
   public abstract String getName();
}
