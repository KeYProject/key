
public class MultiArrayIndexReadWriteAccess {
	public static int compute(int[][] array) {
		if (array != null) {
			if (array.length == 1) {
				if (array[0].length == 1) {
					if (array[0][0] == 42) {
						array[0][0] = 5;
						return array[0][0];
					}
					else {
						return -400;
					}
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
