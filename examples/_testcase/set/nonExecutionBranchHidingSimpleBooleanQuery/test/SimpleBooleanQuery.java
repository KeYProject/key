
public class SimpleBooleanQuery {
	public static int main(boolean x) {
		int magicValue = magic(x);
	    return magicValue;
	}
	
	/*@ normal_behavior
	  @ ensures \result == subMagic(x);
	  @*/
	public /*@ pure @*/ static int magic(boolean x) {
		return subMagic(x);
	}
	
	/*@ normal_behavior
	  @ requires x;
	  @ ensures \result == 42;
	  @
	  @ also
	  @
	  @ normal_behavior
	  @ requires !x;
	  @ ensures \result == -4711;
	  @*/
	public /*@ pure @*/ static int subMagic(boolean x) {
		if (x) {
			return 42;
		}
		else {
			return -4711;
		}
	}
}
