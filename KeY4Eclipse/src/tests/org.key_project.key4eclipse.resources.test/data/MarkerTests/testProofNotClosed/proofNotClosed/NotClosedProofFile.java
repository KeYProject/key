package proofNotClosed;

public class NotClosedProofFile {
	/*@
	  @ ensures \result == x - y;
	  @*/
	public static int add(int x, int y) {
		return x + y;
	}
}
