public class VerifyNumber {
	private int content;

	/*@ normal_behavior
	  @ requires n != null;
	  @ ensures \result == (content == n.content);
	  @ assignable \strictly_nothing;
	  @ also
	  @ exceptional_behavior
	  @ requires n == null;
	  @ signals (Exception) true;
     @ assignable \strictly_nothing;
	  @*/
	public boolean equals(VerifyNumber n) {
		if (content == n.content) {
			return true;
		}
		else {
			return false;
		}
	}
}