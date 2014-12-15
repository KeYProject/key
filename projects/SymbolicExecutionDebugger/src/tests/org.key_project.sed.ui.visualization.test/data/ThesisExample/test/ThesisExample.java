package example5;

public class ThesisExample {
	
	private int intValue;
	
	public int magic(ThesisExample other) {
//		return other.intValue;
		if(intValue == other.intValue) {
			return intValue;
		}
		
		for(int i = 0; i < 1; i++) {
			intValue += i * intValue;
		}
		
		return intValue;
	}
}