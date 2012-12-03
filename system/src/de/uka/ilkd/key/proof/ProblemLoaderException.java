package de.uka.ilkd.key.proof;


public class ProblemLoaderException extends Exception {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 8158433017422914206L;

   private DefaultProblemLoader origin;
   
   public ProblemLoaderException(DefaultProblemLoader origin, Throwable cause) {
      super(cause.getMessage(), cause);
      this.origin = origin;
   }

   public DefaultProblemLoader getOrigin() {
      return origin;
   }
}
