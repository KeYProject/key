
public class WhileTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int main() {
		int result = 0;
		int i = 0;
		while (i < 3) {
			result ++;
			i++;
		}
		return result;
	}

	/*@ requires true;
	  @ ensures true;
	  @*/
	public int mainVariable(int count) {
		int result = 0;
		int i = 0;
		while (i < count) {
			result ++;
			i++;
		}
		return result;
	}
}
