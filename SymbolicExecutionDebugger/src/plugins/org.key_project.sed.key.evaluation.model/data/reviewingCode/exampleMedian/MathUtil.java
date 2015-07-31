/**
 * Provides static methods performing mathematic operations.
 */
public class MathUtil {
   /**
    * Computes the median value between the given start and end index of a sorted array.
    * <p>
    * In case that the number of array elements between start and end is uneven,
    * the median is the value of the array element in the middle between start and end.
    * <p>
    * In case that the number of array elements between start and end is even,
    * the median is the average of the two middle elements.
    * <p>
    * The given array is not modified.
    * @param array The sorted array to compute median for.
    * @param start A valid index in the array representing the lower bound.
    * @param end A valid index in the array representing the upper bound.
    * @return The median value of the array between start and end index.
    */
   public static int median(int[] array, int start, int end) {
      int middle = (start + end) / 2; // TODO: Integer overflow causing later ArrayIndexOutOfBoundsException
      if ((start + end) % 2 == 0) {
         return array[middle];
      }
      else {
         return (array[middle] + array[middle + 1]) / 2;
      }
   }
}
