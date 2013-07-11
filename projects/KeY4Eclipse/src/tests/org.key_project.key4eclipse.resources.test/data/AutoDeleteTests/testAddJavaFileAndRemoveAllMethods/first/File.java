

public class File {
	/*@
	  @ ensures \result == x + y;
	  @*/
	public static int add(int x, int y) {
		return x + y;
	}

	/*@
	  @ ensures \result == x - y;
	  @*/
	public static int sub(int x, int y) {
		return x - y;
	}
}
