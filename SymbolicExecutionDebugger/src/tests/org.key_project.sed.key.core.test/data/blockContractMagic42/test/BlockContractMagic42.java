
public class BlockContractMagic42 {
   public static int fourty;
   
   public static int two;
   
   /*@ normal_behavior
     @ ensures fourty == 40;
     @ ensures two == 2;
     @ ensures \result == 42;
     @ assignable fourty, two;
     @*/
   public static int magic() {
      /*@ normal_behavior
        @ ensures fourty == 40;
        @ ensures two == 2;
        @ assignable fourty, two;
        @*/
      {
         fourty = 40;
         two = 2;
      }
      return fourty + two;
   }
}
