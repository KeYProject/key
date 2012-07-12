
public class FunctionalWhileTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int main() {
		int result = 0;
		int i = 0;
		while (invert(i) > -3) {
			result ++;
			i++;
		}
		return result;
	}

	public int invert(int i) {
		return i * -1;
	}
}
