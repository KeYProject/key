
public class MethodCallOnObject {
	public static int main() {
		MethodCallOnObject x = new MethodCallOnObject();
		return x.doSomething();
	}
	
	public int doSomething() {
		return 42;
	}
}
