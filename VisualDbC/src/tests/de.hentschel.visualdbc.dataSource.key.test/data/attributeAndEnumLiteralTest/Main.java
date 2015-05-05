
public class Main {
	public int intValue;
	
	public MyClass objValue;
	
	/*@ normal_behavior
	  @ requires objValue != null && objValue.enumValue != null;
	  @ ensures true;
	  @*/
	public void main() {
		int temp = intValue;
		temp += objValue.intValue + objValue.enumValue.intValue;
		objValue.enumValue = MyEnum.LITERAL_A;
	}
}
