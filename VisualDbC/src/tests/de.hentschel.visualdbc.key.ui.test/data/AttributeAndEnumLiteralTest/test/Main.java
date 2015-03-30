
public class Main {
	public int mainValue;
	
	public int mainUnused;
	
	public MyClass mainClass;
	
	/*@ requires mainClass != null && c != null && e != null;
	  @ ensures \result == mainValue + mainClass.classValue + c.classValue + e.enumValue + MyEnum.A.enumValue;
	  @*/
	public int main(MyClass c, MyEnum e) {
		return mainValue + mainClass.classValue + c.classValue + e.enumValue + MyEnum.A.enumValue;
	}
}
