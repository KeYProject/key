package ex06;

public class BinarySearch {
	public static int simple(int[] array) {
		if (array != null && array.length >= 10) {
			int index = (array.length + 2) / 2;
			return array[index];
		}
		else {
			return -11;
		}
	}
	
	public static int binarySearch(int[] array, int value) {
		int min = 0;
		int max = array.length - 1;
		/*@ loop_invariant min >= 0 && min < array.length;
		  @ loop_invariant max >= 0 && max < array.length;
		  @ decreasing max - min + 1;
		  @ assignable \strictly_nothing;
		  @*/
		while (max >= min) {
			int middle = (max + min) / 2;
			if (array[middle] == value) {
				return middle;
			}
			else if (array[middle] < value) {
				min = middle + 1;
			}
			else {
				max = middle - 1;
			}
		}
		return -1;
	}
	
	
	
	public static void main(String[] args) {
		int[] array = {0, 1, 2, 3, 4};
////		int[] array = new int[Integer.MAX_VALUE];
//		System.out.println(binarySearch(array, 0));
//		System.out.println(binarySearch(array, 1));
//		System.out.println(binarySearch(array, 2));
//		System.out.println(binarySearch(array, 3));
//		System.out.println(binarySearch(array, 4));
//		System.out.println(binarySearch(array, 50));
//		System.out.println(binarySearch(array, -10));
	}
}
