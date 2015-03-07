
public class NestedDoWhileTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int main() {
		int result = 0;
		int i = 0;
		do {
			do {
				do {
					result ++;
					i++;
				}
				while (i < 2);
				result ++;
				i++;
			}
			while (i < 3);
			result ++;
			i++;
		}
		while (i < 3);
		return result;
	}
}
