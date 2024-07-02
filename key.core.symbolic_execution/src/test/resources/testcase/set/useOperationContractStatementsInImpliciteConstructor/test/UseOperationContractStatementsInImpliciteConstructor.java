
public class UseOperationContractStatementsInImpliciteConstructor {
	public int average(int[] array) {
		if (array != null) {
			int sum = sum(array);
			return sum / array.length;
		}
		else {
			throw new IllegalArgumentException("Array can't be null.");
		}
	}
	
	/*@ normal_behavior
	  @ requires array != null;
	  @ ensures \result == (\sum int i; 0 <= i && i < array.length; array[i]);
	  @*/
	public int sum(int[] array) {
	}
}
