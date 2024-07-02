public class ArrayCreationInstanceTest {
   private int[] array;
   
   //@ requires n >= 4;
   public static int[] main(ArrayCreationInstanceTest obj, int n) {
      obj.array = new int[n];
      obj.array[0] = 100;
      obj.array[1] = obj.array[2];
      obj.array[3] = obj.array[0];
      return obj.array;
   }
}
