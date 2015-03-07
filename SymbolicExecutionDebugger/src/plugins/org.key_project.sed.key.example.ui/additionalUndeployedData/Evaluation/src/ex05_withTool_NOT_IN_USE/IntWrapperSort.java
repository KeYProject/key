package ex05_withTool_NOT_IN_USE;

class IntWrapper {
	public int value;

	public IntWrapper(int value) {
		this.value = value;
	}
}

class BubbleSort {
	public static void sort(IntWrapper[] array) {
		if (array != null) {
			for (int i = 1; i < array.length; i++) {
				for (int j = array.length - 1; j >= i; j--) {
					if (array[j].value < array[j - 1].value) {
						swap(array[j], array[j - 1]);
					}
				}
			}
		}
	}

	private static void swap(IntWrapper first, IntWrapper second) {
		first.value = first.value + second.value;
		second.value = first.value - second.value;
		first.value = first.value - second.value;
	}
}

public class IntWrapperSort {
	public static void main(String[] args) {
		IntWrapper[] array = { new IntWrapper(4), new IntWrapper(3), new IntWrapper(8), new IntWrapper(5) };
		print("Before: ", array);
		BubbleSort.sort(array);
		print("After:  ", array);
	}
	
	private static void print(String text, IntWrapper[] array) {
		System.out.print(text);
		boolean afterFirst = false;
		for (IntWrapper value : array) {
			if (afterFirst) {
				System.out.print(", ");
			}
			else {
				afterFirst = true;
			}
			System.out.print(value.value);
		}
		System.out.println();
	}
}
