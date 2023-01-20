
public class FunctionalForTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int main() {
		int result = 0;
		for (int i = 0; invert(i) > -3; i++) {
			result ++;
		}
		return result;
	}

	public int invert(int i) {
		return i * -1;
	}
}
