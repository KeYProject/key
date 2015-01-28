
public class MultiplePredicateResultsTest {
   private int value;
   
   /*@ normal_behavior
     @ requires x != null && y != null;
     @ ensures \result == 5;
     @*/
   public static int main(MultiplePredicateResultsTest x, MultiplePredicateResultsTest y) {
      x.value = 2;
      y.value = 3;
      return x.value + y.value;
   }
}
