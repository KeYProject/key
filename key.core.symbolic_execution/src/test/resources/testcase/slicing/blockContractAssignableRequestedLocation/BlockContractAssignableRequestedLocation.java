
public class BlockContractAssignableRequestedLocation {
   public static int x;
   
   public static int y;
   
   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static int main() {
      x = 2;
      y = 3;
      /*@ normal_behavior
        @ requires true;
        @ ensures true;
        @ assignable x;
        @*/
      {
         x = -2;
      }
      return x;
   }
}
