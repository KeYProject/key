package ex02;

public class Account {
   /**
    * The currently available amount of money.
    */
   private int balance;
	
   /**
    * The lower limit of {@link #balance} which is {@code 0} or a negative value. 
    * Thus {@code balance >= overdraftLimit} always hold.
    */
	private int overdraftLimit; // overdraftLimit <= 0
	
	/**
	 * A positive value limiting the amount of money the customer
	 * can withdraw from the account per day.
	 */
	private int dailyLimit; // dailyLimit >= 0
	
	/**
	 * Counts the withdrawn money of the current day. 
	 * It is automatically set to {@code 0} every day.
	 */
	private int withdraw = 0; // withdraw >= 0
	
	public boolean update(int amount) {
      int newBalance = balance + amount;
      if (amount < 0) {
         int newWithdraw = withdraw - amount;
         if (newWithdraw < dailyLimit) { // Has to be >
            return false;
         }
         withdraw = newWithdraw; // Has to be after if
         if (newBalance < overdraftLimit) {
            return false;
         }
      }
      balance = newBalance;
      return true;
   }
	
	public static void main(String[] args) {
	   Account a = new Account();
	   a.balance = 0;
	   a.overdraftLimit = 6;
	   a.dailyLimit = 10;
	   System.out.println(a.update(5));
	   System.out.println(a.update(2));
	   System.out.println(a.update(-3));
	   System.out.println(a.update(-3));
	}
}
