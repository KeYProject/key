
public class WhileWithLoopInvariantInCondition {
	public static int size(int[] array) {
		int result = 0;
		int i = 0;
		/*@ loop_invariant i >= 0 && i <= array.length && result == i;
		  @ decreasing array.length - i;
		  @ assignable \strictly_nothing;
		  @*/
		while (goOnNice(array, i)) {
			result++;
			i++;
		}
		return result;
	}
	
	public static boolean goOnNice(int[] array, int i) throws RuntimeException {
		/*@ loop_invariant i == -1;
		  @ decreasing i;
		  @ assignable \strictly_nothing;
		  @*/
		while (i >= 0) {
			i--;
		}
		return true;
	}
}
