
public class SimpleConditionExample {
	
	private int z;
	
	public void main() {
		z = 3;
		while (z >= 0) {
			z--; // Breakpoint with y == 1
		}
	}
	
	public static int somethingMain() {
		int a = 2;
		int b = 3;
		return something(a, b);
	}
	
	public static int something(int a, int b) {
		return a + b;
	}
	
	public static int somethingLocalMain() {
		int y = 42;
		int x = somethingLocal(y);
		somethingLocal(x);
		return y;
	}
	
	public static int somethingLocal(int x) {
		int y = x*x;
		x++;
		return y;
	}
	
}
