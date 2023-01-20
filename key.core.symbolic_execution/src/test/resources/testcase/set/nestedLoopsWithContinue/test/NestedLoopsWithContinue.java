
public class NestedLoopsWithContinue {
	/*@ ensures \result == 10;
	  @*/
	public static int main() {
		int[] array = {1, 2, 3, 4};
		return sum(array);
	}
	
	/*@ requires array != null;
	  @ ensures \result == (\sum int j; 0 <= j && j < array.length; j);
	  @*/
	public static int sum(int[] array) {
		int result = 0;
		int i = -1;
		outer: while (i < array.length - 1) {
			i++;
//			/*@ loop_invariant i >= 0 && i <= array.length && result == (\sum int j; 0 <= j && j < i; array[j]);
//			  @ decreasing array.length - i;
//			  @ assignable \strictly_nothing;
//			  @*/
			int j = 0;
			while (true) {
				result++;
				if (j == i) {
					continue outer;
				}
				j++;
			}
		}
		return result;
	}
}
