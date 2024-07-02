
public class BlockContractVarRenamedLater {
   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public static int main() {
      {
         int x = 0; // x in KeY
      }
      {
         int x = 1; // x_1 in KeY
      }
      {
         int x = 2; // x_2 in KeY
         int y = 3;
         /*@ normal_behavior
           @ requires x == 2;
           @ ensures x == -2;
           @ assignable x;
           @*/
         {
            x = -2;
         }
         return x;
      }
   }
}
