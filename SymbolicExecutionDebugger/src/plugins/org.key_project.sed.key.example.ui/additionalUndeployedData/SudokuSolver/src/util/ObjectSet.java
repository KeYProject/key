package util;

public class ObjectSet extends ObjectList {
   public boolean add(Object value) {
      if (contains(value)) {
         return false;
      }
      else {
         return super.add(value);
      }
   }
}
