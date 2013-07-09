
public class QueryWithFields {
	private int instanceField;
	
	private static int classField;
	
	public int main(int x) {
		int magicValue = magic(x);
	    return magicValue;
	}
	
	/*@ 
	  @ ensures \result == subMagic(x);
	  @*/
	public /*@ pure @*/ int magic(int x) {
		return subMagic(x);
	}
	
	/*@ requires x >= 0 && (instanceField == 11 && classField == 66);
	  @ ensures \result == 421166;
	  @
	  @ also
	  @
	  @ requires x >= 0 && (instanceField != 11 || classField != 66);
	  @ ensures \result == 42;
	  @
	  @ also
	  @
	  @ requires x < 0;
	  @ ensures \result == -4711;
	  @*/
	public /*@ pure @*/ int subMagic(int x) {
		if (x >= 0) {
			if (instanceField == 11 && classField == 66) {
				return 421166;
			}
			else {
				return 42;
			}
		}
		else {
			return -4711;
		}
	}
}
