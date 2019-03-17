
public class ArrayAverage {
	public static int average(int[] array) throws Exception {
		int sum = sum(array);
		return sum / array.length;
	}
	
	/*@ normal_behavior
	  @ requires array != null;
	  @ ensures \result == (\sum int i; 0 <= i && i < array.length; array[i]);
	  @
	  @ also
	  @
	  @ exceptional_behavior
	  @ requires array == null;
	  @ signals (Exception e) true;
	  @*/
	public static int sum(/*@ nullable @*/ int[] array) throws Exception {
		if (array == null) {
			throw new Exception();
		}
		else {
			int sum = 0;
			/*@ loop_invariant i >= 0;
			  @ loop_invariant i <= array.length;
			  @ loop_invariant sum == 
			  @                 (\sum int j; 
			  @                       0 <= j && j < i; 
			  @                       array[j]);
			  @ decreasing array.length - i;
			  @ assignable \strictly_nothing;
			  @*/
			for (int i = 0; 
			     i < array.length; i++) {
				sum += array[i];
			}
			return sum;
		}
	}		
}
