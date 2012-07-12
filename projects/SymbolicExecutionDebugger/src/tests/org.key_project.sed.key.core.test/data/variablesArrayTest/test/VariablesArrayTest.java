
public class VariablesArrayTest {
	public int main() {
		int[][] multiArray = new int[2][];
		multiArray[0] = new int[] {1, 2};
		multiArray[1] = new int[] {3, 4, 5};
		return multiArray[0][0] + multiArray[0][1] +
		       multiArray[1][0] + multiArray[1][1] + multiArray[1][2];
	}
}
