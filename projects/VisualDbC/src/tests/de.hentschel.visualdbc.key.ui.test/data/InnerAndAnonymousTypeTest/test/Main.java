
public class Main {
	/*@
	  @ ensures true;
	  @*/
	public int main() {
		IGetter getter = new IGetter() {
			public int getValue() {
				return 0;
			}
		};
		return getter.getValue() +
			   InnerInterface.VALUE + 
			   InnerInterface.InnerInterfaceInterface.VALUE + 
               InnerInterface.InnerInterfaceClass.VALUE +
               InnerClass.VALUE +
               InnerClass.InnerClassInterface.VALUE +
               InnerClass.InnerClassClass.VALUE +
               InnerEnum.VALUE +
               InnerEnum.InnerEnumClass.VALUE +
               InnerEnum.InnerEnumInterface.VALUE;
//               InnerEnum.InnerEnumEnum.VALUE;
	}
	
	public interface IGetter {
		public int getValue();
	}
	
	public class InnerInterface {
		public static final int VALUE = 1;

		public class InnerInterfaceInterface {
			public static final int VALUE = 2;
		}

		public class InnerInterfaceClass {
			public static final int VALUE = 3;
		}
	}

	public class InnerClass {
		public static final int VALUE = 4;
		
		public class InnerClassInterface {
			public static final int VALUE = 5;
		}

		public class InnerClassClass {
			public static final int VALUE = 6;
		}
	}

	public enum InnerEnum {
		INNER_LITERAL;
		
		public static final int VALUE = 7;
		
		public class InnerEnumInterface {
			public static final int VALUE = 8;
		}

		public class InnerEnumClass {
			public static final int VALUE = 9;
		}

//		public enum InnerEnumEnum {
//			INNER_ENUM_LITERAL;
//			
//			public static final int VALUE = 10;
//		}
	}
}
