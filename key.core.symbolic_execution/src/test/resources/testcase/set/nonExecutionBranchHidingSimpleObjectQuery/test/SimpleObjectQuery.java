
public class SimpleObjectQuery {
	public static final Object INSTANCE = new Object();
	
	public static int main(Object x) {
		int magicValue = magic(x);
	    return magicValue;
	}
	
	/*@ normal_behavior
	  @ ensures \result == subMagic(x);
	  @*/
	public /*@ pure @*/ static int magic(Object x) {
		return subMagic(x);
	}
	
	/*@ normal_behavior
	  @ requires x == INSTANCE;
	  @ ensures \result == 42;
	  @
	  @ also
	  @
	  @ normal_behavior
	  @ requires x != INSTANCE;
	  @ ensures \result == -4711;
	  @*/
	public /*@ pure @*/ static int subMagic(Object x) {
		if (x == INSTANCE) {
			return 42;
		}
		else {
			return -4711;
		}
	}
}
