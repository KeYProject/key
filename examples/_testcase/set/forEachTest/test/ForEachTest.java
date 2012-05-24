
public class ForEachTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int main() {
		int[] array = new int[3];
		int result = 0;
		for (int element : array) {
			result ++;
		}
		return result;
	}

	/*@ requires true;
	  @ ensures true;
	  @*/
	public int mainVariable(int[] array) {
		int result = 0;
		for (int element : array) {
			result ++;
		}
		return result;
	}
}
