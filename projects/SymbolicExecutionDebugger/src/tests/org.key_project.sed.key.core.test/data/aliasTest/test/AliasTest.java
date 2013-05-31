
public class AliasTest {
	public int array(IntWrapper w, IntWrapper[] array) {
		w.value = 1;
		array[0].value = 2;
		array[1].value = 3;
		return w.value + array[0].value + array[1].value;
	}
	
	public int main(IntWrapper a, IntWrapper b) {
		a.value = 2;
		b.value = 3;
		return a.value + b.value;
	}
	
	private static class IntWrapper {
		public int value;
	}
}
