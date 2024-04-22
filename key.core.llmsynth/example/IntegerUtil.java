
public class IntegerUtil {
    /*@ public normal_behavior
      @ requires true;
      @ ensures \result == a - (-b);
      @*/
   public static int add(int a, int b) {
      return sub(a, -b);
   }
   
   /*@ normal_behavior
      ensures \result == x - y;
     @*/
   public static int sub(int x, int y) {
      return x - y;
   }
}
