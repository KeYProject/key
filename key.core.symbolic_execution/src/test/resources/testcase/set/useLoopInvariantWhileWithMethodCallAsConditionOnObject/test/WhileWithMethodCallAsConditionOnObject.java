
public class WhileWithMethodCallAsConditionOnObject {
	public int size(WhileWithMethodCallAsConditionOnObject x, int[] array) {
		int result = 0;
		int i = 0;
		/*@ loop_invariant i >= 0 && i <= array.length && result == i;
		  @ decreasing array.length - i;
		  @ assignable \strictly_nothing;
		  @*/
		while (x.goOnNice(array, i)) {
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
	  @ signals (RuntimeException myExc) true;
	  @*/
	public boolean goOnNice(/*@ nullable @*/ int[] array, int i) throws RuntimeException {
		throw new RuntimeException();
	}
}
