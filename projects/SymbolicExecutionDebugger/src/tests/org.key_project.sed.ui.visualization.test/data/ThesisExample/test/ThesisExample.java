package example5;

public class ThesisExample {
	
	private int intValue;
	
	public int magic(ThesisExample other) {
		if(intValue == other.intValue) {
			for(int j = 0; j < 1; j++) {
				intValue -= j * intValue;
			}
		}
		else {
			for(int i = 0; i < 2; i++) {
				intValue += i * intValue;
			}
		}

		return intValue;
	}
}