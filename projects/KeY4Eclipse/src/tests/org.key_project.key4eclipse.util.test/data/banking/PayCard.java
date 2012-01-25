package banking;

public class PayCard {
	private /*@ spec_public @*/ int balance;
	
	public PayCard() {
	}
	
	/*@ requires amount >= 0;
	  @ ensures balance == \old(balance) + amount;
	  @*/
	public void charge(int amount) {
		this.balance += amount;
	}
	
	public void x() {
		 int x = 2 + 3;
	}
}
