public class Arrays {
   public static int indexOf(Object[] array, Filter filter) {
      int acceptedIndex = -1;
      int i = 0;
      /*@ loop_invariant i >= 0 && i <= array.length;
        @ decreasing array.length - i;
        @ assignable \strictly_nothing;
        @*/
      while (acceptedIndex < 0 && i < array.length) {
         if (filter.accept(array[i])) {
            acceptedIndex = i;
         }
         i++;
      }
      return acceptedIndex;
   }

   public static interface Filter {
      /*@ normal_behavior
        @ requires true;
        @ ensures true;
        @ assignable \strictly_nothing;
        @*/
      public boolean accept(/*@ nullable @*/ Object object);
   }
}