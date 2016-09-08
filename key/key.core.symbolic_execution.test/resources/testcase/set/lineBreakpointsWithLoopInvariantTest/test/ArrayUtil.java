public class ArrayUtil {
	/*@ normal_behavior
	  @ ensures \result >= 0 && \result < array.length 
	  @         ==> array[\result] == toSearch;
	  @ ensures \result >= 0 && \result < array.length 
	  @         ==> (\forall int i; i >= 0 && i < \result; 
	  @                      array[i] != toSearch);
	  @ ensures \result == -1 
	  @             <==> (\forall int i; i >= 0 && i < array.length; 
	  @                           array[i] != toSearch);
	  @ assignable \strictly_nothing;
	  @*/
	public static int indexOf(Object[] array, Object toSearch) {
		int i =  0;
		/*@ loop_invariant i >= 0 && i <= array.length;
		  @ loop_invariant (\forall int j; j >= 0 && j < i; 
		  @                         array[j] != toSearch);
		  @ decreasing array.length - i;
		  @ assignable \strictly_nothing;
		  @*/
		while (i < array.length) {
			if (toSearch == array[i]) { return i; }
			i++;
		}
		return 0;
	}
}