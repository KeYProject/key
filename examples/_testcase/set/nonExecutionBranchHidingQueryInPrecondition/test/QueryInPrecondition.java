
public class QueryInPrecondition {
	public static int main(int x, int y) {
		int magicValue = magic(x, y);
	    return magicValue;
	}
	
	/*@ requires xPre(x) && y < 0;
	  @ ensures \result == subFirst(x, y);
	  @ also
	  @ requires !(xPre(x) && y < 0);
	  @ ensures \result == subSecond(x, y);
	  @*/
	public /*@ pure @*/ static int magic(int x, int y) {
		return subFirst(x, y);
	}
	
	/*@ requires xPre(x) && y < 0;
	  @ ensures \result == 42;
	  @*/
	public /*@ pure @*/ static int subFirst(int x, int y) {
		if (x >= 0 && y < 0) {
			return 42;
		}
		else {
			return 0;
		}
	}
	
	/*@ 
	  @ ensures \result == x >= 0;
	  @*/
	public /*@ pure @*/ static boolean xPre(int x) {
		if (x >= 0) {
			return true;
		}
		else {
			return false;
		}
	}
	
	/*@ requires !(x >= 0 && y < 0);
	  @ ensures \result == -4711;
	  @*/
	public /*@ pure @*/ static int subSecond(int x, int y) {
		if (!(x >= 0 && y < 0)) {
			return -4711;
		}
		else {
			return 0;
		}
	}
}
