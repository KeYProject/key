public class EmptyArrayCreationTest {
   private int[] array;
   
   //@ requires n == 0;
   public static int[] compute(EmptyArrayCreationTest obj, int n) {
      obj.array = new int[n];
      return obj.array;
   }
}
