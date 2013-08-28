
public class VerifiedTest {
	/*@ exceptional_behavior
	  @ requires true;
	  @ signals (Exception) true;
	  @*/
	public static int magicException() throws Exception {
		throw new Exception();
	}
	
	/*@ exceptional_behavior
	  @ requires true;
	  @ signals_only RuntimeException;
	  @ signals (RuntimeException) true;
	  @*/
	public static int notMagicException() throws Exception {
		throw new Exception();
	}
	
	/*@
	  @ ensures \result == 42;
	  @*/
	public static int magic() {
		return 42;
	}

	/*@ 
	  @ ensures \result == 42;
	  @*/
	public static int notMagic() {
		return 66;
	}
	
	/*@
	  @ ensures \result == 0;
	  @*/
	public static int loop(int x) {
		if (x < 0) {
			x = -x;
		}
		/*@ loop_invariant x >= 0;
		  @ decreasing x;
		  @*/
		while (x > 0) {
			x--;
		}
		return x;
	}
	
	/*@
	  @ ensures \result == 0;
	  @*/
	public static int notLoop(int x) {
		if (x < 0) {
			x = -x;
		}
		/*@ loop_invariant x >= 0;
		  @ decreasing x;
		  @*/
		while (x > 0) {
			x -= 2;
		}
		return x;
	}
}
