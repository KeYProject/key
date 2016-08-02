/**
 * Provides static methods performing mathematically operations.
 */
public class MathUtil {
   /**
    * Computes the median value between the given start and end index of a 
    * sorted array without modifying it. The relation between start and end
    * is not important. This means that the median is computed in case that
    * {@code start <= end} holds but also in case that {@code start > end} holds.
    * <p>
    * In case that the number of array elements between start and end is odd (uneven),
    * the median is the value of the array element in the middle of start and end.
    * <p>
    * In case that the number of array elements between start and end is even,
    * the median is the average (integer division) of the two middle elements.
    * @param array The sorted array for which to compute the median.
    * @param start A valid index in the array.
    * @param end A valid index in the array.
    * @return The median value of the array between start and end index.
    * @throws IllegalArgumentException in case of illegal parameters.
    */
   public static int median(int[] array, int start, int end) {
      // Check parameters
      if (array == null) {
         throw new IllegalArgumentException("Array is null.");
      }
      if (start < 0 || start >= array.length) {
         throw new IllegalArgumentException("Start is not within the array bounds.");
      }
      if (end < 0 || end >= array.length) {
         throw new IllegalArgumentException("End is not within the array bounds.");
      }
      // Compute median
      int middle = (start + end) / 2;
      if ((start + end) % 2 == 0) {
         return array[middle];
      }
      else {
         return (array[middle] + array[middle + 1]) / 2;
      }
   }
}