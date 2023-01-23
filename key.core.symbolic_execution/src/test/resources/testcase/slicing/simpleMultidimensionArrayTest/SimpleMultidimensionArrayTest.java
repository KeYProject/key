
public class SimpleMultidimensionArrayTest {
   /*@ normal_behavior
     @ requires \invariant_for(array);
     @ requires array.length == 4;
     @ requires array[0].length == 4;
     @ requires array[1].length == 4;
     @ requires array[2].length == 4;
     @ requires array[3].length == 4;
     @ ensures true;
     @*/
   public static int main(int[][] array) {
      array[0][0] = 40;
      array[1][1] = 2;
      array[2][2] = -4711;
      array[3][3] = array[0][0] + array[1][1];
      return array[3][3];
   }
}
