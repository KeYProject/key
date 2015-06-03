public class Account {
   private int balance;
   
   /*@ normal_behavior
     @ requires amount > 0;
     @ ensures balance == \old(balance) - \result;
     @ ensures \result == amount;
     @*/
   public int checkAndWithdraw(int amount) {
      if (canWithdraw(amount)) {
         withdraw(amount);
         return amount;
      }
      else {
         return 0;
      }
   }

   /*@ normal_behavior
     @ requires amount > 0;
     @ ensures balance == \old(balance) - amount;
     @ assignable balance;
     @*/
   public void withdraw(int amount) {
      balance -= amount;
   }

   /*@ normal_behavior
     @ requires amount > 0;
     @*/
   public /*@ pure @*/ boolean canWithdraw(int amount) {
      return amount > 0;
   }
   
   /*@ normal_behavior
     @ ensures \result == balance;
     @*/
   public /*@ pure @*/ int getBalance() {
      return balance;
   }
}