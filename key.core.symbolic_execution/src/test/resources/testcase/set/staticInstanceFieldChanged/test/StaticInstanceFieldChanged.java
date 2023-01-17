
public class StaticInstanceFieldChanged {
	public static DirectValue instance;
   public static NextValue nextInstance;
	
	public int magic() {
      nextInstance.dvalue = new DirectValue();
	   nextInstance.dvalue.value = 24;
		instance.value = 42;
		return instance.value + nextInstance.dvalue.value;
	}
	
	private static class DirectValue {
	   public int value;
	}
	
	private static class NextValue {
      public DirectValue dvalue;
	}
}
