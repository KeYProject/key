/**
 * Provides the basic functionality to perform a linear search.
 * @see ValueSearch
 */
public abstract class AbstractSearch {
   /**
    * Performs a linear search without modifying the given array.
    * @param array The array to search in.
    * @return The index of the first found element or 
    *         {@code -1} if no element was found.
    */
   public int search(int[] array) {
      /*@ loop_invariant i >= 0 && i <= array.length;
        @ decreasing array.length - i;
        @ assignable i;
        @*/
      for (int i = 0; i < array.length; i++) {
         if (accept(array, i)) {
            return i;
         }
      }
      return -1;
   }

   /**
    * Checks if an element is found.
    * @param array The array in which the search is performed in.
    * @param index The current array index to check.
    * @return {@code true} element found, {@code false} element not found.
    */
   protected abstract boolean accept(int[] array, int index);
}
