public class VariableArrayIndex {
	private int[] array;
	private int index;

	// array != null && array.length >= 1 && index >= 0 && index < array.length
	public int compute() {
		array[index] = 42;
		return array[index];
	}
}
