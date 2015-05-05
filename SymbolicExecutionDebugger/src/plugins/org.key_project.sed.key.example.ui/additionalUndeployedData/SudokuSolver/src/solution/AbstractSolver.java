package solution;

public abstract class AbstractSolver {
   public boolean solve() {
      return solve(true);
   }

   protected boolean solve(boolean allowGuessing) {
      boolean somethingChanged = removeInvalidValues();
      if (allowGuessing && !isSolved()) {
         if (guessValue()) {
            somethingChanged = true;
         }
      }
      return somethingChanged;
   }
   
   protected abstract boolean removeInvalidValues();
   
   protected abstract boolean guessValue();

   public abstract boolean isValid();
   
   public abstract boolean isSolved();
}
