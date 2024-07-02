
public class NestedForTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int main() {
		int result = 0;
		for (int i = 0; i < 3; i++) {
			for (; i < 3; i++) {
				for (; i < 2; i++) {
					result ++;
				}
				result ++;
			}
			result ++;
		}
		return result;
	}
}
