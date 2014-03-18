package example2;

import java.util.Arrays;

/**
 * This example explains how to find the origin of a bug with the help of the 
 * Symbolic Execution Debugger (SED). 
 * <p>
 * The debugging session starts directly with the method of interest:
 * <ol>
 *    <li>
 *       Debug method {@link #sort()} via context menu item 
 *       'Debug As, Symbolic Execution Debugger (SED)'
 *    </li>
 *    <li>Select the start node</li>
 *    <li>
 *       In view 'Debug', Perform 'Step Into' until a node representing an 
 *       uncaught {@link NullPointerException} appears (3 times)
 *    </li>
 * </ol>
 * The encountered {@link NullPointerException} is spurious as field 
 * {@link #numbers} cannot be {@code null}. This kind of knowledge can be added 
 * by providing a precondition:
 * <ol> 
 *    <li>Terminate the debug session</li>
 *    <li>
 *       Open the debug configuration via main menu item 
 *       'Run, Debug Configurations'
 *    </li>
 *    <li>Add {@code numbers != null & numbers.length >= 1} as precondition</li>
 *    <li>Debug method {@link #sort()} as before</li>
 *    <li>Select the start node</li>
 *    <li>
 *       In view 'Debug', Perform 'Step Into' until the next statement after the 
 *       if-statement is reached (5 times)
 *    </li>
 * </ol>
 * Two observations: First, because of the precondition no spurious exceptions 
 * are shown any longer. Second, because of the if-statement one would expect 
 * two branches. The fact that there is only one indicates a problem with the 
 * if-guard (which evaluates always to true). The guard needs to be 
 * corrected to {@code low < high}.
 * <p>
 * <b>Taken from:</b> <br>
 * Visual Interactive Debugger Based on Symbolic Execution
 * Reiner Hähnle, Markus Baum, Richard Bubel, and Marcel Rothe
 * 25th IEEE/ACM International Conference on Automated Software Engineering 
 * (Antwerp, Belgium), ASE 2010 
 */
public class QuickSort {
	private int[] numbers;

	public QuickSort(int[] numbers) {
	   assert numbers != null;
	   assert numbers.length >= 1;
		this.numbers = numbers;
	}

	public void sort() {
		sort(0, numbers.length - 1);
	}

	private void sort(int low, int high) {
		if (low <= high) {
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