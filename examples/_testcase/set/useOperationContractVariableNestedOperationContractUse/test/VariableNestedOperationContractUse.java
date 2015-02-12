
public class VariableNestedOperationContractUse {
   public static int main(int x) {
      return doubleMagic(magic(x));
   }

   /*@ normal_behavior
     @ ensures \result == x + x;
     @*/
   public static /*@ strictly_pure @*/ int doubleMagic(int x) {
      return x + x;
   }
   
   /*@ normal_behavior
     @ ensures \result > x;
     @*/
   public static /*@ strictly_pure @*/ int magic(int x) {
      return x + 1;
   }
}
