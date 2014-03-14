import java.util.Random;

public class QuickSortExample {
	public static void main(String[] args) {
		// Create array with random numbers
		int[] numbers = new int[5];
		Random random = new Random();
		for (int i = 0; i < numbers.length; i++) {
			numbers[i] = random.nextInt(numbers.length);
		}
		// Create QuickSort
		QuickSort sorter = new QuickSort(numbers);
		// Print unsorted array
		System.out.println(sorter);
		// Sort array
		sorter.sort();
		// Print sorted array
		System.out.println(sorter);
	}
}
