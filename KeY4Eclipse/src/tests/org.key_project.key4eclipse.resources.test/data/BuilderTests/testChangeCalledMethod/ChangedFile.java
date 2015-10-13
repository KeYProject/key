
public class File {
	/*@
	  @ ensures \result == x + y;
	  @*/
	public static int add(int x, int y) {
		return identity(x) + identity(y);
	}
	
	public static int identity(int x) {
		return x + 1;
	}
}
