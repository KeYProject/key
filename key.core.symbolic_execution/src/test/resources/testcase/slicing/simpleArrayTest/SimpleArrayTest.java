
public class SimpleArrayTest {
   /*@ normal_behavior
     @ requires \invariant_for(array);
     @ requires array.length == 4;
     @ ensures true;
     @*/
   public static int main(int[] array) {
      array[0] = 40;
      array[1] = 2;
      array[2] = -4711;
      array[3] = array[0] + array[1];
      return array[3];
   }
}
