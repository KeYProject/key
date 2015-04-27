package file.two;

public class SecondFile {
	/*@
	  @ ensures \result == x + y;
	  @*/
	public static int add(int x, int y) {
		return x + y;
	}
}
