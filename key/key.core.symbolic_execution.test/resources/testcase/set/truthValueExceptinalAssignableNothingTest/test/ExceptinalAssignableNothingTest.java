
public class ExceptinalAssignableNothingTest {
   /*@ exceptional_behavior
     @ signals (NullPointerException) true;
     @ assignable \nothing;
     @*/
   public static void main() {
      throw new NullPointerException();
   }
}
