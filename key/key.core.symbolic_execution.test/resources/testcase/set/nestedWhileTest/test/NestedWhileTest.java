
public class NestedWhileTest {
	/*@ requires true;
	  @ ensures true;
	  @*/
	public int mainNested() {
		int result = 0;
		int i = 0;
		while (i < 3) {
			while (i < 3) {
				while (i < 2) {
					result ++;
					i++;
				}
				result ++;
				i++;
			}
			result ++;
			i++;
		}
		return result;
	}
}
