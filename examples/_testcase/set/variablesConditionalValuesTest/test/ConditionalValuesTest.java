
public class ConditionalValuesTest {
   private int value;
   
   public static int main(ConditionalValuesTest x, ConditionalValuesTest y) {
      x.value = 2;
      y.value = 3;
      return x.value + y.value;
   }
   
   public static int mainNext(Both b) {
      b.x.value = 2;
      b.y.value = 3;
      return b.x.value + b.y.value;
   }
   
   private static class Both {
      public ConditionalValuesTest x;
      public ConditionalValuesTest y;
   }
}
