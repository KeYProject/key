
public class FunctionalDoWhileTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int main() {
		int result = 0;
		int i = 0;
		do {
			result ++;
			i++;
		}
		while (invert(i) > -3);
		return result;
	}

	public int invert(int i) {
		return i * -1;
	}
}
