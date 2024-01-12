
public class ArrayInstanceCreationTest {
	public static int[] classArray;
	
	public int[] instanceArray;
	
	public ArrayInstanceCreationTest next;
	
	public int compute() {
		ArrayInstanceCreationTest.classArray = new int[] {1};
		instanceArray = new int[] {2};
		if (next != null) {
			next.instanceArray = new int[] {3};
			int[] localArray = {4, 5};
//			return classArray[0] + instanceArray[0] + next.instanceArray[0] + localArray[0] + localArray[1];
			return localArray[0] + localArray[1];
		}
		else {
			return -100;
		}
	}
}
