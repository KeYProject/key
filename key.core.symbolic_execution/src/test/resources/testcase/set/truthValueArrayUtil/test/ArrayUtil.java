public class ArrayUtil {
	/*@ normal_behavior
	  @ requires \invariant_for(filter);
	  @*/
	public static int /*@ strictly_pure @*/ indexOf(Object[] array, 
	                                                Filter filter) {
		int index = -1;
		int i = 0;
		/*@ loop_invariant i >= 0 && i <= array.length;
		  @ decreasing array.length - i;
		  @ assignable \strictly_nothing;
		  @*/
		while (index < 0 && i < array.length) {
			if (filter.accept(array[i])) {
				index = i;
			}
			else {
				i++;
			}
		}
		return i;
	}
	
	public static interface Filter {
		/*@ normal_behavior
		  @ requires true;
		  @ ensures true;
		  @*/
		public boolean /*@ strictly_pure @*/ accept(/*@ nullable @*/ Object object);
	}
}