
public class ArraySumForEach {
	/*@ requires array != null;
	  @ ensures \result == (\sum int j; 0 <= j && j < array.length; array[j]);
	  @*/
	public static int sum(int[] array) {
		int result = 0;
		/*@ loop_invariant \index >= 0 && \index <= array.length && result == (\sum int j; 0 <= j && j < \index; array[j]);
		  @ decreasing array.length - \index;
		  @ assignable \strictly_nothing;
		  @*/
		for (int value : array) {
			result += value;
		}
		return result;
	}
}
