public final class IntegerUtil {
	/*@ normal_behavior
	  @ ensures \result == x + y;
	  @ assignable \strictly_nothing;
	  @*/
	public static int add(int x, int y) {
		return x + y;
	}
	
	/*@ normal_behavior
	  @ ensures \result == x - y;
	  @ assignable \strictly_nothing;
	  @*/
	public static int sub(int x, int y) {
		return x + y;
	}
}