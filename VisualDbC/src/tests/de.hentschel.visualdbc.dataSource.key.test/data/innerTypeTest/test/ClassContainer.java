import interfaces.MyInterface;

public class ClassContainer {
	class DefaultChildClass {
		private int x;
		
		public DefaultChildClass(int x) {
			this.x = x;
		}
		
		public void run() {
			new MyInterface() {
			};
		}
	}

	private static class PrivateChildClass {
		public interface InnerInnerInterface {
			
		}
	}

	protected abstract class ProtectedChildClass {
	}
	
	public final class PublicChildClass {
		public class InnerInnerClass {
			public void innerInnerRun() {
				new MyInterface() {
				};
			}
		}
	}

	interface DefaultChildInterface {
		public interface InnerInnerInterface {
		}
		
		public class InnerInnerClass {
			public void innerInnerRun() {
				new MyInterface() {
				};
			}
		}
	}

	private static interface PrivateChildInterface {
	}

	protected interface ProtectedChildInterface {
	}
	
	public abstract interface PublicChildInterface {
	}
	
	public void doContainer() {
		new MyInterface() {
		};
	}
	
	
	
	
	enum DefaultChildEnum {
		INSTANCE(42);
		
		private int x;
		
		private DefaultChildEnum(int x) {
			this.x = x;
		}
		
		public void run() {
			new MyInterface() {
			};
		}
	}

	private static enum PrivateChildEnum {
		INSTANCE;
		
//		public enum InnerInnerEnum {
//			INSTANCE;
//		}
	}

	protected enum ProtectedChildEnum {
	}
	
	public enum PublicChildEnum {
		INSTANCE;
		
//		public enum InnerInnerEnum {
//			INSTANCE;
//			
//			public void innerInnerRun() {
//				new MyInterface() {
//				};
//			}
//		}
	}
}