package b;

public class B {
	/*@ normal_behavior
	  @ requires x < y;
	  @ ensures \result == x;
	  @ also
	  @ normal_behavior
	  @ requires x >= y;
	  @ ensures \result == y;
	  @*/
	public static int min(int x, int y) {
		if (x < y) {
			return x;
		}
		else {
			return x;
		}
	}
}
