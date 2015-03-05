
public class ExceptionalMethodReturnTest {
   public static int main(IntWrapper x) {
      try {
         return first(x);
      }
      catch (Exception e) {
         return 42;
      }
   }
   
   public static int first(IntWrapper x) {
      return second(x);
   }
   
   public static int second(IntWrapper x) {
      return x.value;
   }
   
   private static class IntWrapper {
      public int value;
   }
}
