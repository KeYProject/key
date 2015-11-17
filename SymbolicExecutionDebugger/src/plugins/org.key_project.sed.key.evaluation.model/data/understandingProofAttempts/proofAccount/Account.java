public class Account {
   private int balance;
   
   /*@ normal_behavior
     @ requires amount > 0;
     @ ensures balance == \old(balance) - amount;
     @ ensures \result == amount;
     @ assignable balance;
     @*/
   public int checkAndWithdraw(int amount) {
      if (canWithdraw(amount)) {
         withdraw(amount);
         return amount; //XXX: Termination 1
      }
      else {
         return 0; //XXX: Termination 2
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
     @ ensures true;
     @ assignable \nothing;
     @*/
   public boolean canWithdraw(int amount) {
      return amount > 0;
   }
   
   /*@ normal_behavior
     @ requires true;
     @ ensures \result == balance;
     @ assignable \nothing;
     @*/
   public int getBalance() {
      return balance;
   }
}