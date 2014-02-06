package d;

public class SameName {
	/*@ normal_behavior
	  @ requires true;
	  @ ensures \result == 42123;
	  @*/
	public static int d() {
		return 42123;
	}
}
