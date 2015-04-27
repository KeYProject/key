
public class File {
	/*@
	  @ ensures \result == x + y;
	  @*/
	public static int add(int x, int y) {
		return identity(x) + identity(y);
	}
	
	/*@
	  @ ensures \result == x - y;
	  @*/
	public static int sub(int x, int y) {
		return x - y;
	}
	
	/*@
	  @ ensures \result == x;
	  @*/
	public static int identity(int x) {
		return x;
	}
}
