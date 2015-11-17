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
    * @param array The array in which the search is performed.
    * @param value The value to search (search criteria).
    * @return The index of the first found element or 
    *         {@code -1} if no element was found.
    */
   public static int find(int[] array, int value) {
      return new ValueSearch().search(array);
   }
   
   /**
    * Accepts an array index if it's value is equal to {@link #value}.
    * @param array The array in which the search is performed.
    * @param index The current array index to check.
    * @return {@code true} value at {@code array[index]} is equal to {@link #value}, {@code false} otherwise.
    */
   protected boolean accept(int[] array, int index) {
      if (index < 0 || index >= array.length) {
         return false;
      }
      else {
         return array[index] == value;
      }
   }
   
   public static void main(String[] args) {
      // TODO: Write executable code here if appropriate.
      //System.out.println(ValueSearch.find(new int[] {arrayElementsSeparatedByComma}, value));
   }
}