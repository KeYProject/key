
public class MethodCallOnObjectWithException {
	public static int main() {
		try {
			MethodCallOnObjectWithException x = new MethodCallOnObjectWithException();
			return x.doSomething();
		}
		catch (NullPointerException e) {
			MethodCallOnObjectWithException y = new MethodCallOnObjectWithException();
			return y.return42();
		}
	}
	
	public int doSomething() {
		MethodCallOnObjectWithException x = null;
		return x.return42();
	}
	
	public int return42() {
		return 42;
	}
}
