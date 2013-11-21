public class IndexOf {
	/*@ normal_behavior
	  @ requires array != null && comperator != null && \invariant_for(comperator);
	  @ ensures true;
	  @*/
	public static int indexOf(final Object[] array, final Object toSearch, final Comperator comperator) {
		int index = -1;
		int i = 0;
		/*@ loop_invariant i >= 0 && i <= array.length;
		  @ decreasing array.length - i;
		  @ assignable \strictly_nothing;
		  @*/
		while (index < 0 && i <= array.length) { // i < array.length
			if (!comperator.equals(array[i], toSearch)) { // remove the not
				index = i;
			}
			i++;
		}
		return i; // return index
	}
	
	public static interface Comperator {
		/*@ normal_behavior
		  @ requires true;
		  @ ensures true;
		  @*/
		public boolean /*@ strictly_pure @*/ equals(Object first, Object second);
	}
}
