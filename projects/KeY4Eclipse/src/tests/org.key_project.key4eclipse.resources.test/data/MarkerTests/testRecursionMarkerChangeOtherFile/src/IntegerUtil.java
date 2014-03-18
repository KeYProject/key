public class IntegerUtil {
	/*@ normal_behavior
	  @ requires true;
	  @ ensures \result == x + y;
	  @*/
	public static /*@ pure @*/ int add(int x, int y) {
		if (x >= 0) {
			return x + y;
		}
		else {
			return x + y;
		}
	}
	
	/*@ normal_behavior
	  @ requires true;
	  @ ensures \result == x - y;
	  @*/
	public static /*@ pure @*/ int sub(int x, int y) {
		return x + y;
	}
}