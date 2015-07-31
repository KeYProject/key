/**
 * Provides a linear search to find a given value.
 * @see AbstractSearch
 */
public class ValueSearch extends AbstractSearch {
   /**
    * The value to search.
    */
   private int value;

   /**
    * Performs a linear search to find the first array index 
    * containing the given value. The array is not modified by the search.
    * @param array The array to search in.
    * @param value The value to search.
    * @return The index of the first found element or 
    *         {@code -1} if no element was found.
    */
   public static int find(int[] array, int value) {
      return new ValueSearch().search(array);
   }
   
   /**
    * Checks if an element is found which is the case
    * when it is equal to {@link #value}.
    * @param array The array in which the search is performed in.
    * @param index The current array index to check.
    * @return {@code true} element found, {@code false} element not found.
    */
   protected boolean accept(int[] array, int index) {
      if (index < 0 || index >= array.length) {
         return false;
      }
      else {
         return array[index] == value;
      }
   }
}
