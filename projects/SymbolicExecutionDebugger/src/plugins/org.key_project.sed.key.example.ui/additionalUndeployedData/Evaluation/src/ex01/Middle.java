package ex01;
// Page 255
public class Middle {
	public static int middle(int x, int y, int z) {
		if (y < z) {
			if (x < y) {
				return y;
			}
			else if (x < z) {
				return y;
			}
		}
		else {
			if (x > y) {
				return y;
			}
			else if (x > z) {
				return x;
			}
		}
		return z;
	}
	
	public static void doTest(int x, int y, int z) {
//		System.out.println(x + ", " + y + ", " + z + " = " + middle(x, y, z));
	}
	
	public static void main(String[] args) {
		doTest(3, 3, 5);
		doTest(1, 2, 3);
		doTest(3, 2, 1);
		doTest(5, 5, 5);
		doTest(5, 3, 4);
		doTest(2, 1, 3);
	}
}
