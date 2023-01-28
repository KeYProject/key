public class ArrayAssignmentTest {
   //@ requires array.length >= 4;
   public static int[] main(int[] array) {
      array[0] = 100;
      array[1] = array[2];
      array[3] = array[0];
      return array;
   }
}
