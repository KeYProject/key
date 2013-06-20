package method.changed;

public class JavaFile {
	/*@
	  @ ensures \result == x + y + 1;
	  @*/
	public static int add(int x, int y) {
		return x + y;
	}
}
