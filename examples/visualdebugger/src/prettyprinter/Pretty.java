package prettyprinter;

import java.util.Random;

/**
 * The Class Pretty.
 * 
 * Created to expose when displayed branch conditions become unreadable in the
 * Visual Debugger.
 */
public class Pretty {

	/** The my array. */
	int[] myArray;

	/**
	 * The main method.
	 * 
	 * @param args
	 *            the arguments
	 */
	public static void main(String[] args) {

		Pretty pretty = new Pretty();
		pretty.initMyArray(50);
		pretty.complexDemo();
		
	}

	/**
	 * Complex Demo.
	 * 
	 * This method creates a branched execution tree to show malformed
	 * branchconditions, i.e. not readable for humans.
	 * A randomly initialized integer array is used build up 
	 *  
	 * @return the int
	 * 
	 * required minimal jml spec to make the VD work
	 */
	/*@ public normal_behavior requires true; ensures true; @*/
	public int complexDemo() {

		int result = 0;
		if (max(myArray) < 50) {
			if (max(myArray) < 30) {
				result = 30;
			} else {
				if (max(myArray) < 20) {
					result = 20;
				} else {
					if (max(myArray) < 10)
						result = 10;

				}
			}
		} else {
		if (max(myArray) > 50) {
			if (max(myArray) > 60) {
				result = 60;
			} else {
				if (max(myArray) > 70) {
					result = 70;
				} else {
					if (max(myArray) > 80)
						result = 80;

				}
			}
		} }
		return result;
	}

	/**
	 * Simple Demo.
	 * 
	 * This method creates a branched execution tree to show malformed
	 * branchconditions, i.e. not readable for humans.
	 * 
	 * @param i -
	 *            a integer
	 * 
	 * @return the int
	 * 
	 * required minimal jml spec to make the VD work:
	 */
	/*@ public normal_behavior requires true; ensures true; @*/
	public int simpleDemo(int i) {

		if (i < 50) {
			if (i < 30) {
				return 30;
			} else {
				if (i < 20) {
					return 20;
				} else {
					if (i < 10)
						return 10;

				}
			}
		}
		if (i > 50) {
			if (i > 60) {
				return 60;
			} else {
				if (i > 70) {
					return 70;
				} else {
					if (i > 80)
						return 80;

				}
			}
		}
		return i;
	}

	// some helper methods
	/**
	 * Inits myArray.
	 * 
	 * @param max
	 *            the upper bound for the array values
	 * 
	 * @return the int[]
	 */
	public int[] initMyArray(int max) {

		myArray = new int[10];
		Random nextValue = new Random();
		for (int i = 0; i < 10; i++) {
			myArray[i] = nextValue.nextInt(max);
		}

		return myArray;
	}

	/**
	 * Max.
	 * 
	 * Returns the maximum value of an array.
	 * 
	 * @param values
	 *            the array
	 * 
	 * @return the int
	 * 
	 */
	public int max(int[] values) {

		int max = values[0];
		int i = 0;
		while (i < values.length) {
			int j = values[i++];
			if (j > max) {
				max = j;
			}
		}
		return max;
	}
}
