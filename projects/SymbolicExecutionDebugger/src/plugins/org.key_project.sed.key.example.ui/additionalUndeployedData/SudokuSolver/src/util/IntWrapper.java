package util;

public final class IntWrapper {
   public final int value;

   public IntWrapper(int value) {
      this.value = value;
   }

   public int hashCode() {
      return value;
   }

   public boolean equals(Object obj) {
      if (obj instanceof IntWrapper) {
         return value == ((IntWrapper)obj).value;
      }
      else {
         return false;
      }
   }

   public String toString() {
      return value + "";
   }
}
