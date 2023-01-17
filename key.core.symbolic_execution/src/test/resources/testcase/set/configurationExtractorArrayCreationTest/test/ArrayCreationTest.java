public class ArrayCreationTest {
   private static int[] array;
   
   //@ requires n >= 4;
   public static int[] compute(int n) {
      array = new int[n];
      array[0] = 100;
      array[1] = array[2];
      array[3] = array[0];
      return array;
   }
}
