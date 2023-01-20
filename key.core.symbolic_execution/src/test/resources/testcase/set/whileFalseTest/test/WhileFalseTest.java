
public class WhileFalseTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int main() {
		int result = 0;
		while (false) {
			result ++;
		}
		return result;
	}
}
