package org.key_project.util.java;

public final class IntegerUtil {
   /**
    * Forbid instances.
    */
   private IntegerUtil() {
   }
   
   /**
    * Computes the factorial value of n.
    * @param n The value.
    * @return The computed factorial value or {@code -1} if n is negative.
    */
   public static int factorial(int n) {
      if (n < 0) {
         return -1;
      }
      else {
         int factorial = 1;
         for (int i = 1; i <= n; i++) {
            factorial *= i;
         }
         return factorial;
      }
   }
}
