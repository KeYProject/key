
public class File {
	/*@
      @ public normal_behavior
	  @ ensures \result == x + y;
	  @
      @ public normal_behavior
	  @	ensures \result >= 0;
	  @*/
	public static int add(int x, int y) {
		return x + y;
	}
}
