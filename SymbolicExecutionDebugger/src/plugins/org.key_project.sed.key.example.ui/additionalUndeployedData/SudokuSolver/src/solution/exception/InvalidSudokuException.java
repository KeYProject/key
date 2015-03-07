package solution.exception;

public class InvalidSudokuException extends RuntimeException {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 2415927685142157916L;

   public InvalidSudokuException() {
      super();
   }

   public InvalidSudokuException(String message, Throwable cause) {
      super(message, cause);
   }

   public InvalidSudokuException(String message) {
      super(message);
   }

   public InvalidSudokuException(Throwable cause) {
      super(cause);
   }
}
