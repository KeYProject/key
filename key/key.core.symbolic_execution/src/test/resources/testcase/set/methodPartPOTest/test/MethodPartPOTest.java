
public class MethodPartPOTest {
	private int field;
	
	public static final int CONSTANT = 2;
	
	public void voidMethod(boolean x, int y) {
		if (x) {
			int a = 2 * y;
		}
		else {
			int b = 3 * y;
			return;
		}
	}
	
	public int doSomething(int asdf, String a, boolean b) {
		int x = 0;
		if (asdf < 0) {
			x = x * -1;
			x += 2;
		}
		else {
			x -= 42;
			return x;
		}
		x = 1 * asdf;
		int y = 2 + MethodPartPOTest.CONSTANT + field;
		int doubleValue = doubleValue(x);
		int z = x + y + doubleValue;
		return z;
	}
	
	private int doubleValue(int value) {
		int result;
		result = value + value;
		return result;
	}
}
