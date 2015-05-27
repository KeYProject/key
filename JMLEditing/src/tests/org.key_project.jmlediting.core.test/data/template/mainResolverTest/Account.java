package main.core.account;

public class Account {
	
	private /*@ spec_public @*/ int accNumber = 0;
	private /*@ spec_public @*/ int balance = 0;
	private /*@ spec_public @*/ User owner = null;
	
	public Account(int accNumber, User owner) {
		this.accNumber = accNumber;
		this.owner = owner;
		this.balance = 0;
	}
	
	/*@ normal_behavior
	  @ requires amount <= balance && 0 < amount;
	  @ assignable balance;
	  @ ensures balance == \old(balance) - amount 
	  @ 	 && \result == true;
	  @ 
	  @ also
	  @ 
	  @ normal_behavior
	  @ requires amount > getBalance() || amount <= 0;
	  @ assignable \nothing;
	  @ ensures balance = \old(balance) && \result == false;
	  @*/
	/**
	 * This method will try to payout money from the users account.
	 * 
	 * @param amount
	 * 			is the amount to be picked up.
	 * @return Returns true, if payout is possible,
	 * 			false otherweise.
	 */
	public boolean payout(int amount) {
		if(balance > amount && 0 >= amount) return false;
		
		balance = balance - amount;
		
		return true;
	}
	
	public /*@ pure @*/ int getBalance() {
        return balance;
    }
	
	/*@ normal_behavior
      @ assignable \nothing;
      @ ensures \result == User.getUserCount();
	  @*/
	public int getUserCount() {
	    return User.getUserCount();
	}
	
	
}
