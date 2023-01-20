
public class SimpleConstructorTest {
	private int x;

	public SimpleConstructorTest(int x) {
		super();
		this.x = x;
	}
	
	public static int main() {
		SimpleConstructorTest obj = new SimpleConstructorTest(42);
		return obj.x;
	}
}
