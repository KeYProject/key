
public class ArrayIndexVariableTest {
   private int value;
   
   /*@ normal_behavior
     @ requires x >= 0;
     @ requires x < array.length - 2;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static int main(ArrayIndexVariableTest[] array, int x) {
      array[x].value = 40;
      array[x + 1].value = 2;
      int result = array[x].value + array[x + 1].value;
      return result;
   }
}
