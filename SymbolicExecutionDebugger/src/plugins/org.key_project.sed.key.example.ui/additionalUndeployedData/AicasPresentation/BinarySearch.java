package example6;

public class BinarySearch {
	public static int search(int[] array, int target) {
		int low = 0;
		int high = array.length - 1;
		while (low <= high) {
			int mid = (low + high) / 2;
			if (target < array[mid]) {
				high = mid - 1;
			} else if (target > array[mid]) {
				low = mid + 1;
			} else {
				return mid;
			}
		}
		return -1;
	}
}
