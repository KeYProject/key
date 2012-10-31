/*******************************************************************************
 * Copyright (c) 2011 Martin Hentschel.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Martin Hentschel - initial API and implementation
 *******************************************************************************/

package packageA.B.C;

import interfaces.MyInterface;

public enum EnumContainer {
	INSTANCE;
	
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
	
	
	
	
//	enum DefaultChildEnum {
//		INSTANCE(42);
//		
//		private int x;
//		
//		private DefaultChildEnum(int x) {
//			this.x = x;
//		}
//		
//		public void run() {
//			new MyInterface() {
//			};
//		}
//	}

//	private static enum PrivateChildEnum {
//		INSTANCE;
//		
//		public enum InnerInnerEnum {
//			INSTANCE;
//		}
//	}

//	protected enum ProtectedChildEnum {
//	}
//	
//	public enum PublicChildEnum {
//		INSTANCE;
//		
//		public enum InnerInnerEnum {
//			INSTANCE;
//			
//			public void innerInnerRun() {
//				new MyInterface() {
//				};
//			}
//		}
//	}
}
