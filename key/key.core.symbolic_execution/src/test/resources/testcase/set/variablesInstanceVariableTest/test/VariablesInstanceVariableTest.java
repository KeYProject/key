public class VariablesInstanceVariableTest {
	private int a;
	
	private int b;
	
	private IntWrapper wrapper;
	
	public int main(IntWrapper param) {
		int x = 5;
		a = x;
		b = 3;
		param = new IntWrapper();
		param.value = 1;
		wrapper = new IntWrapper();
		wrapper.value = 4;
		return a + b + x + wrapper.value + param.value;
	}
}

class IntWrapper {
	public int value;
}
