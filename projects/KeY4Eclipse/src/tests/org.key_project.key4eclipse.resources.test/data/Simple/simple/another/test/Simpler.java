package simple.another.test;

public class Simpler {
	/*@ 
	  @ ensures \result == x / y;
	  @*/
	public static int div(int x, int y) {
		return x / y;
	}

	/*@
	  @ ensures \result == x * y;
	  @*/
	public static int mul(int x, int y) {
		return x * y;
	}
}
