
public class MethodCallReturnTests {
	public static int staticValue;
	
	private int value;
	
	public int main() {
		noReturn();
		emptyReturn();
		valueReturn(); // Ignore result
		int returnedValue1 = valueReturn();
		noReturnStatic();
		emptyReturnStatic();
		valueReturnStatic(); // Ignore result
		int returnedValue2 = valueReturnStatic();
		return returnedValue1 + returnedValue2;
	}
	
	public static void noReturnStatic() {
		staticValue = 0;
	}
	
	public static void emptyReturnStatic() {
		staticValue++;
		return;
		staticValue = 42;
	}
	
	public static int valueReturnStatic() {
		staticValue++;
		return staticValue;
		staticValue = 4711;
	}
	
	public void noReturn() {
		value = 0;
	}
	
	public void emptyReturn() {
		value++;
		return;
		value = 43;
	}
	
	public int valueReturn() {
		value++;
		return value;
		value = 4712;
	}
}
