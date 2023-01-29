public class ArrayUtil {
   /*@ normal_behavior
     @ ensures array == null || array.length == 0 ==> \result == -1;
     @ ensures array != null && array.length >= 1 ==> (\forall int i; i >= 0 && i < array.length; array[\result] <= array[i]);
     @ assignable \nothing;
     @*/
   public static int minIndex(/*@ nullable @*/ int[] array) {
      if (array != null) {
         if (array.length == 0) {
            return -1; //XXX: Termination 1
         }
         else {
            if (array.length == 1) {
               return array[0]; //XXX: Termination 2
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
                     //XXX: Loop Body Termination  1 (of the 'Body Preserves Invariant' branch)
                  }
                  else {
                     //XXX: Loop Body Termination 2 (of the 'Body Preserves Invariant' branch)
                  }
               }
               return minIndex; //XXX: Termination 3
            }
         }
      }
      else {
         return -1; //XXX: Termination 4
      }
   }
}
