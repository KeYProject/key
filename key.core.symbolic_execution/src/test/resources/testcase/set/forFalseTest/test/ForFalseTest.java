
public class ForFalseTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int main() {
		int result = 0;
		for (int i = 0; false; i++) {
			result ++;
		}
		return result;
	}
}
