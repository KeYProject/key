package example2;

import java.util.Random;

/**
 * An example application using the sorting algorithm implemented in class 
 * {@link QuickSort}. For more details, read the documentation of 
 * {@link QuickSort}. Have fun finding the bug!
 * <p>
 * <b>Taken from:</b> <br>
 * Visual Interactive Debugger Based on Symbolic Execution
 * Reiner Hähnle, Markus Baum, Richard Bubel, and Marcel Rothe
 * 25th IEEE/ACM International Conference on Automated Software Engineering 
 * (Antwerp, Belgium), ASE 2010 
 */
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