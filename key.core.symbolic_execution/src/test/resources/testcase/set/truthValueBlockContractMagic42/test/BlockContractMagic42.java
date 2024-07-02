
public class BlockContractMagic42 {
   public static int fourty;
   
   public static int two;
   
   /*@ normal_behavior
     @ requires fourty == 40;
     @ ensures two == 2;
     @ ensures \result == 42;
     @ assignable two;
     @*/
   public static int magic() {
      int numberTwo;
      /*@ normal_behavior
        @ requires fourty == 40;
        @ ensures numberTwo == 2;
        @ ensures two == 2;
        @ assignable two;
        @*/
      {
         numberTwo = 2;
         two = numberTwo;
      }
      return fourty + two;
   }
}
