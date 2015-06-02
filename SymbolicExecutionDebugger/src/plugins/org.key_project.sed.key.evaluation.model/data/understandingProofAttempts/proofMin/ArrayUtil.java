public class ArrayUtil {
   /*@ normal_behavior
     @ ensures array == null || array.length == 0 ==> \result == -1;
     @ ensures array != null && array.length >= 1 ==> (\forall int i; i >= 0 && i < array.length; array[\result] <= array[i]);
     @ assignable \nothing;
     @*/
   public static int minIndex(/*@ nullable @*/ int[] array) {
      if (array != null) {
         if (array.length == 0) {
            return -1; // Return 1
         }
         else if (array.length == 1) {
            return array[0]; // Return 2
         }
         else {
            int minIndex = 0;
            /*@ loop_invariant i >= 1 && i <= array.length;
              @ loop_invariant minIndex >= 0 && minIndex < i;
              @ loop_invariant (\forall int j; j >= 0 && j < i; 
              @                         array[minIndex] <= array[j]);
              @ decreases array.length - i;
              @ assignable minIndex, i;
              @*/
            for (int i = 1; i < array.length; i++) {
               if (array[i] < array[minIndex]) {
                  minIndex = 1;
                  // Loop End 1
               }
               else {
                  // Loop End 2
               }
            }
            return minIndex; // Return 3
         }
      }
      else {
         return -1; // Return 4
      }
   }
}
