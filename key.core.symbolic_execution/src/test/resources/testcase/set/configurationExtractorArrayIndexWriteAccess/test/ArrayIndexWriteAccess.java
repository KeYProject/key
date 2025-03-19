
public class ArrayIndexWriteAccess {
	public static int compute(int[] array) {
		if (array != null) {
			if (array.length == 1) {
				array[0] = 42;
				return array[0];
			}
			else {
				return -200;
			}
		}
		else {
			return -100;
		}
	}
}
