
public class ArrayLength {
	private int length;
	
	private int[] array;
	
	private MyClass my;
	
	/*@ requires array != null && my != null && my.array != null;
	  @ ensures true;
	  @*/
	public int main() {
		int result = 0;
		result += length;
		result += array.length;
		result += my.length;
		result += my.array.length;
		return result;
	}
	
	public static class MyClass {
		public int length;
		
		public int[] array;
	}
}
