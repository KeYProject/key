
public class ArrayIndexAsVariableFieldTest {
   private int value;
   
   /*@ normal_behavior
     @ requires \invariant_for(index);
     @ requires index.value >= 0;
     @ requires index.value < array.length - 2;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static int main(ArrayIndexAsVariableFieldTest[] array, Index index) {
      array[index.value].value = 40;
      array[index.value + 1].value = 2;
      int result = array[index.value].value + array[index.value + 1].value;
      return result;
   }
   
   private static class Index {
      int value;
   }
}
