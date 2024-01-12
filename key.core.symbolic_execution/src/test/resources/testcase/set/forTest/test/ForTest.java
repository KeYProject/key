
public class ForTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int main() {
		int result = 0;
		for (int i = 0; i < 3; i++) {
			result ++;
		}
		return result;
	}

	/*@ requires true;
	  @ ensures true;
	  @*/
	public int mainVariable(int count) {
		int result = 0;
		for (int i = 0; i < count; i++) {
			result ++;
		}
		return result;
	}
}
