
public class ArrayIndexSideeffectsBevore {
   /*@ normal_behavior
     @ requires value >= 0;
     @ requires value < array.length - 2;
     @ ensures \result == 42;
     @ assignable \everything;
     @*/
   public static int mainBevore(int[] array, int value) {
      array[++value] = 42;
      array[++value] = 4711;
      int result = array[value - 1];
      return result;
   }
}
