
public class DoWhileTest {
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
		while (i < 3);
		return result;
	}

	/*@ requires true;
	  @ ensures true;
	  @*/
	public int mainVariable(int count) {
		int result = 0;
		int i = 0;
		do {
			result ++;
			i++;
		}
		while (i < count);
		return result;
	}
}
