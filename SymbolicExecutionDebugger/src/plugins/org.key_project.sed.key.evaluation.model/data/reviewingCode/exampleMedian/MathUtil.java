public class MathUtil {
   /**
    * Computes the median value between the given start and end index.
    * @param array The sorted array to compute median for.
    * @param start A valid index in the array representing the lower bound.
    * @param end A valid index in the array representing the upper bound.
    * @return The median value of the array between start and end index.
    */
   public static int median(int[] array, int start, int end) {
      int middle = (start + end) / 2;
      if ((start + end) % 2 == 0) {
         return array[middle];
      }
      else {
         return (array[middle] + array[middle + 1]) / 2;
      }
   }
}
