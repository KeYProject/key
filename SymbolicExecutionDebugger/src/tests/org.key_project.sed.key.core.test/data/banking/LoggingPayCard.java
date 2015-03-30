package banking;

public class LoggingPayCard extends PayCard {
	private /*@ spec_public @*/ int[] log = new int[10];
	
	/*@ public invariant (nextEntry >= 0 & nextEntry < log.length); @*/
	private /*@ spec_public @*/ int nextEntry = 0;
	
	/*@ also
	  @ requires amount >= 0;
	  @ ensures log[\old(nextEntry)] == amount;
	  @ ensures \old(nextEntry) + 1 != log.length ? 
	  @         nextEntry == \old(nextEntry) + 1 : nextEntry == 0;
	  @ ensures (\forall int i; i >= 0 & i < log.length & 
	  @         i != \old(nextEntry); log[i] == \old(log[i]));
	  @*/
	public void charge(int amount) {
		super.charge(amount);
		log[nextEntry] = amount;
		nextEntry = nextEntry < log.length - 1 ? nextEntry + 1 : 0;
	}
}
