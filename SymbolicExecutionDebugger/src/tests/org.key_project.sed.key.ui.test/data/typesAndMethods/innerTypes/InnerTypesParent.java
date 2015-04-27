package innerTypes;

public class InnerTypesParent {
	public @interface InnerAnnotation {
		public @interface InnerInnerAnnotation {
			public String methodInInnerInnerAnnotation();
		}

		public String methodInInnerAnnotation();
	}
	
	public enum InnerEnum {
		A,
		B;
		
		public enum InnerInnerEnum {
			C,
			D;
			
			public void methodInInnerInnerEnum() {
			}
		}
		
		public void methodInInnerEnum() {
		}
	}
	
	public interface InnerInterface {
		public interface InnerInnerInterface {
			public void methodInInnerInnerInterface();
		}
		
		public void methodInInnterInterface();
	}
	
	public class InnerClass {
		public class InnerInnerClss {
			public void methodInInnerInnerClass() {
			}
		}
		
		public void methodInInnerClass() {
		}
	}
}
