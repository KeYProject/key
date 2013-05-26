public class ConfigurationExtractorWithOperationContractsTest {
   public static int compute(IntWrapper x, IntWrapper y) {
		x.value = 2;
		y.value = 3;
		int add = sub(x, y);
		return add;
	}
	
	/*@ 
	  @ ensures \result == x.value + y.value;
	  @ */
	public static int sub(IntWrapper x, IntWrapper y) {
		throw new RuntimeException();
	}
	
	private static class IntWrapper {
		public int value;
	}
}
