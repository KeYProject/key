
public class ArrayIndexReadAccess {
	public static int compute(int[] array) {
		if (array != null) {
			if (array.length == 1) {
				if (array[0] == 42) {
					return 42;
				}
				else {
					return -300;
				}
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
