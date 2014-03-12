package game.event;

public interface SudokuListener {
   public void possibleValueRemoved(SudokuEvent event);
   
   public void valueSet(SudokuEvent event);
}
