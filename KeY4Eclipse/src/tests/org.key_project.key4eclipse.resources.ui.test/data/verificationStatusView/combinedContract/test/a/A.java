package a;

import b.B;

public class A {
	/*@ normal_behavior
	  @ ensures x < y ==> \result == x;
	  @ ensures x >= y ==> \result == y;
	  @*/
	public static int min(int x, int y) {
		return B.min(x, y);
	}
}
