package game.event;


public class SudokuListenerList {
   private SudokuListener[] array = new SudokuListener[0];
   
   public SudokuListenerList() {
      
   }

   public int size() {
      return array.length;
   }
   
   public SudokuListener get(int index) {
      return array[index];
   }

   public boolean isEmpty() {
      return size() == 0;
   }
   
   public int indexOf(SudokuListener value) {
      for (int i = 0; i < array.length; i++) {
         if (array[i].equals(value)) {
            return i;
         }
      }
      return -1;
   }

   public boolean contains(SudokuListener value) {
      return indexOf(value) >= 0;
   }

   public void clear() {
      array = new SudokuListener[0];
   }

   public void remove(int index) {
      if (index >= 0 && index < array.length) {
         SudokuListener[] newArray = new SudokuListener[array.length - 1];
         for (int i = 0; i < index; i++) {
            newArray[i] = array[i];
         }
         for (int i = index + 1; i < array.length; i++) {
            newArray[i - 1] = array[i];
         }
         array = newArray;
      }
      else {
         throw new RuntimeException();
      }
   }

   public boolean remove(SudokuListener value) {
      int index = indexOf(value);
      if (index >= 0) {
         remove(index);
         return true;
      }
      else {
         return false;
      }
   }

   public SudokuListener[] toArray() {
      return array;
   }

   public boolean add(SudokuListener value) {
      SudokuListener[] newArray = new SudokuListener[array.length + 1];
      for (int i = 0; i < array.length; i++) {
         newArray[i] = array[i];
      }
      newArray[array.length] = value;
      array = newArray;
      return true;
   }
}
