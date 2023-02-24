
public class WhileWithMethodCallAsCondition {
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
	  @*/
	public static boolean goOn(/*@ nullable @*/ int[] array, int i) {
		throw new RuntimeException();
	}
	
	/*@ normal_behavior
	  @ requires array != null;
	  @ ensures \result == i < array.length;
	  @*/
	public static boolean goOnExc(int[] array, int i) {
		throw new RuntimeException();
	}
	
	/*@ normal_behavior
	  @ requires array != null && i >= 0;
	  @ ensures \result == i < array.length;
	  @
	  @ also
	  @
	  @ public exceptional_behavior
	  @ requires i < 0;
	  @ signals_only Exception;
	  @ signals (RuntimeException myExc) true;
	  @*/
	public static boolean goOnNice(/*@ nullable @*/ int[] array, int i) throws RuntimeException {
		throw new RuntimeException();
	}
}
