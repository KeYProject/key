
public class SimpleIntQuery {
	public static int main(int x) {
		int magicValue = magic(x);
	    return magicValue;
	}
	
	public static int mainWithUpdates(int x) {
		x = 11;
		int magicValue = magic(x);
	    return magicValue;
	}
	
	public static int mainWithSymbolicUpdates(int x) {
		x = x + 11;
		int magicValue = magic(x);
	    return magicValue;
	}
	
	/*@ normal_behavior
	  @ ensures \result == subMagic(x);
	  @*/
	public /*@ pure @*/ static int magic(int x) {
		return subMagic(x);
	}
	
	/*@ normal_behavior
	  @ requires x >= 0;
	  @ ensures \result == 42;
	  @
	  @ also
	  @
	  @ normal_behavior
	  @ requires x < 0;
	  @ ensures \result == -4711;
	  @*/
	public /*@ pure @*/ static int subMagic(int x) {
		if (x >= 0) {
			return 42;
		}
		else {
			return -4711;
		}
	}
	
	/*@ normal_behavior
	  @ requires true;
	  @ ensures true;
	  @*/
	public /*@ pure @*/ static boolean preCheck(int x) {
		return true;
	}
	
	/*@ normal_behavior
	  @ requires value != null;
	  @ ensures true;
	  @
	  @ also
	  @
	  @ exceptional_behavior
	  @ requires value == null;
	  @ signals (NullPointerException) true;
	  @*/
	public static void exceptionTest(/*@ nullable @*/ String value) throws NullPointerException {
		if (value.length() == 0) {
			return;
		}
	}
}
