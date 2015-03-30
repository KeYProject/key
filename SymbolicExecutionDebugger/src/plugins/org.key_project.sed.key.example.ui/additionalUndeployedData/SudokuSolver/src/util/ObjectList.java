package util;

public class ObjectList {
   public Object[] array = new Object[0];
   
   public ObjectList() {
      
   }

   public ObjectList(ObjectList initial) {
      this.array = initial.array;
   }

   public int size() {
      return array.length;
   }
   
   public Object get(int index) {
      return array[index];
   }

   public boolean isEmpty() {
      return size() == 0;
   }
   
   public int indexOf(Object value) {
      for (int i = 0; i < array.length; i++) {
         if (array[i].equals(value)) {
            return i;
         }
      }
      return -1;
   }

   public boolean contains(Object value) {
      return indexOf(value) >= 0;
   }

   public void clear() {
      array = new Object[0];
   }

   public void remove(int index) {
      if (index >= 0 && index < array.length) {
         Object[] newArray = new Object[array.length - 1];
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

   public boolean remove(Object value) {
      int index = indexOf(value);
      if (index >= 0) {
         remove(index);
         return true;
      }
      else {
         return false;
      }
   }

   public Object[] toArray() {
      return array;
   }

   public boolean add(Object value) {
      Object[] newArray = new Object[array.length + 1];
      for (int i = 0; i < array.length; i++) {
         newArray[i] = array[i];
      }
      newArray[array.length] = value;
      array = newArray;
      return true;
   }
}
