package game;


public class FieldList {
   public Field[] array = new Field[0];
   
   public FieldList() {
      
   }

   public int size() {
      return array.length;
   }
   
   public Field get(int index) {
      return array[index];
   }

   public boolean isEmpty() {
      return size() == 0;
   }
   
   public int indexOf(Field value) {
      for (int i = 0; i < array.length; i++) {
         if (array[i].equals(value)) {
            return i;
         }
      }
      return -1;
   }

   public boolean contains(Field value) {
      return indexOf(value) >= 0;
   }

   public void clear() {
      array = new Field[0];
   }

   public void remove(int index) {
      if (index >= 0 && index < array.length) {
         Field[] newArray = new Field[array.length - 1];
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

   public boolean remove(Field value) {
      int index = indexOf(value);
      if (index >= 0) {
         remove(index);
         return true;
      }
      else {
         return false;
      }
   }

   public Field[] toArray() {
      return array;
   }

   public boolean add(Field value) {
      Field[] newArray = new Field[array.length + 1];
      for (int i = 0; i < array.length; i++) {
         newArray[i] = array[i];
      }
      newArray[array.length] = value;
      array = newArray;
      return true;
   }
}
