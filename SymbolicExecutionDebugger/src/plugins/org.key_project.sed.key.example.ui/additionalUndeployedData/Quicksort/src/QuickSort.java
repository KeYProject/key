import java.util.Arrays;

public class QuickSort {
	private int[] numbers;

	public QuickSort(int[] numbers) {
		this.numbers = numbers;
	}

	public void sort() {
		sort(0, numbers.length - 1);
	}

	private void sort(int low, int high) {
		if (low <= high) { // Correct: low < high
			int middle = partition(low, high);
			sort(low, middle);
			sort(middle + 1, high);
		}
	}

	private int partition(int low, int high) {
		int x = numbers[low];
		int i = low - 1;
		int j = high + 1;

		while (i < j) {
			do {
				j--;
			} while (numbers[j] > x);

			do {
				i++;
			} while (numbers[i] < x);

			if (i < j) {
				int tmp = numbers[i];
				numbers[i] = numbers[j];
				numbers[j] = tmp;
			}
		}
		return j;
	}

	public String toString() {
		return Arrays.toString(numbers);
	}
}