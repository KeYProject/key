
public class SimpleBooleanQuery {
	public static int main(boolean x) {
		int magicValue = magic(x);
	    return magicValue;
	}
	
	/*@ 
	  @ ensures \result == subMagic(x);
	  @*/
	public /*@ pure @*/ static int magic(boolean x) {
		return subMagic(x);
	}
	
	/*@ requires x;
	  @ ensures \result == 42;
	  @
	  @ also
	  @
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
