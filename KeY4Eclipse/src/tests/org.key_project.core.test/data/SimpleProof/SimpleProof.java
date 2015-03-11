
public class SimpleProof {
	/*@ normal_behavior
	  @ ensures \result == 42;
	  @ assignable \strictly_nothing;
	  @*/
	public static int magic() {
		return 42;
	}
}
