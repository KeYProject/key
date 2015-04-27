
public class WhileWithMethodCallAsConditionFullImplemented {
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
	
	/*@ normal_behavior
	  @ requires array != null && i >= 0;
	  @ ensures \result == i < array.length;
	  @
	  @ also
	  @
	  @ public exceptional_behavior
	  @ requires i < 0;
	  @ signals (RuntimeException myExc) \not_specified;
	  @*/
	public static boolean goOnNice(/*@ nullable @*/ int[] array, int i) throws RuntimeException {
		if (i < 0) {
			throw new RuntimeException();
		}
		else {
			return i < array.length;
		}
	}
}
