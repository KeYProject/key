
public class MethodCallParallelTest {
	public int main() {
		int a = a();
		int x = x();
		return a * x;
	}
	
	public int a() {
		int b1 = b();
		int b2 = b();
		int c = c();
		return b1 + b2 + c;
	}
	
	public int b() {
		return c();
	}
	
	public int c() {
		return 42;
	}
	
	public int x() {
		return 2;
	}
}
