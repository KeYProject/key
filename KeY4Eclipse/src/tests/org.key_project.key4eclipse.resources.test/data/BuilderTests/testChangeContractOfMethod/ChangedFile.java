
public class File {
	/*@
      @ public normal_behavior
	  @ ensures \result == x + y;
	  @
      @ public normal_behavior
	  @ requires x >= 0 && y >= 0;
	  @	ensures \result >= 0;
	  @*/
	public static int add(int x, int y) {
		return x + y;
	}
}
