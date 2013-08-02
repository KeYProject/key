
public class ArraySumWhileWithException {
	public static int sum(int[] array) {
		int result = 0;
		int i = 0;
		/*@ loop_invariant i >= 0 && i <= array.length && result == (\sum int j; 0 <= j && j < i; array[j]);
		  @ decreasing array.length - i;
		  @ assignable \strictly_nothing;
		  @*/
		while (i < array.length) {
			result += array[i];
			i++;
			if (array.length == 3) {
				throw new RuntimeException();
			}
		}
		return result;
	}
}
