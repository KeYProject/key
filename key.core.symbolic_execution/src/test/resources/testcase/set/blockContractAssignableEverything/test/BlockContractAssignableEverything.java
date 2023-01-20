
public class BlockContractAssignableEverything {
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
        @ assignable \everything;
        @*/
      {
         x = -2;
         y = -3;
      }
      return x;
   }
}
