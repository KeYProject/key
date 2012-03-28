
public class FixedRecursiveMethodCallTest {
	public static int decreaseValue() {
		return decrease(3);
	}
	
	public static int decrease(int n) {
		if (n >= 1) {
			return decrease(n - 1);
		}
		return n;
	}
}
