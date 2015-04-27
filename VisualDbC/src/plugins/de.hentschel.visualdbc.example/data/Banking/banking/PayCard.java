package banking;

public class PayCard {
	private /*@ spec_public @*/ int balance;
	
	/*@ requires amount >= 0;
	  @ ensures balance == \old(balance) + amount;
	  @*/
	public void charge(int amount) {
		this.balance += amount;
	}
}
