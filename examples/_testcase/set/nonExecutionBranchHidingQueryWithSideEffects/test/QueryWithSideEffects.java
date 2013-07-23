
public class QueryWithSideEffects {
	private int instanceField;
	
	private static int classField;
	
	public int main(int x) {
		int magicValue = magic(x);
	    return magicValue + instanceField + classField;
	}
	
	/*@ normal_behavior
	  @ ensures \result == subMagic(x);
	  @ ensures x >= 0 ==> instanceField == 12;
	  @ ensures x < 0 ==> instanceField == -21;
	  @ ensures x >= 0 ==> classField == 66;
	  @ ensures x < 0 ==> classField == -55;
	  @*/
	public /*@ pure @*/ int magic(int x) {
		return subMagic(x);
	}
	
	/*@ normal_behavior
	  @ requires x >= 0;
	  @ ensures \result == 42;
	  @ ensures instanceField == 12;
	  @ ensures classField == 66;
	  @
	  @ also
	  @
	  @ normal_behavior
	  @ requires x < 0;
	  @ ensures \result == -4711;
	  @ ensures instanceField == -21;
	  @ ensures classField == -55;
	  @*/
	public /*@ pure @*/ int subMagic(int x) {
		if (x >= 0) {
			return 42;
		}
		else {
			return -4711;
		}
	}
}
