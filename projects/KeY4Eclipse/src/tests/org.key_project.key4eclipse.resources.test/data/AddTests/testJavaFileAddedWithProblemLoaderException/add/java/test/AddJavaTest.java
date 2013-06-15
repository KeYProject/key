package add.java.test;

public class AddJavaTest {
	/*@
	  @ ensures \result == x + y;
	  @*/
	public static int add(int x, int y) {
		return x + y;
	}

	/*@
	  @ ensu res \result == x - y;
	  @*/
	public static int sub(int x, int y) {
		return x - y;
	}
}
