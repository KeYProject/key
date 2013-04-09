
public class VoidWhileWithReturn {
	public static void sum(int[] array) {
		int result = 0;
		int i = 0;
		/*@ loop_invariant i >= 0 && i <= array.length && result == (\sum int j; 0 <= j && j < i; array[j]);
		  @ decreasing array.length - i;
		  @ assignable \strictly_nothing;
		  @*/
		while (true) {
			if (array == null) {
				return;
			}
			else if (i == array.length) {
				return;
			}
			result += array[i];
			i++;
		}
	}
}
