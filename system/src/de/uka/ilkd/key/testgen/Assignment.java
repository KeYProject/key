package de.uka.ilkd.key.testgen;

/** This class creates either assignments or creates calls to setter methods to initiate fields.  
 * @author gladisch
 * @author herda
 */
public class Assignment {
	

		protected final String type;
		protected final Object left;
		protected final String right;

		public Assignment(String left, String right) {
			type = "";
			this.left = left;
			this.right = right;
		}

		/** The argument left of type RefEx must contains all needed information to invoke a setter method.*/
		public Assignment(RefEx left, String right) {
			type = "";
			this.left = left;
			this.right = right;
		}

		public Assignment(String type, Object left, String right) {
			this.type = type;
			this.left = left;
			this.right = right;
		}

		@Override
		public String toString() {
			return type + " " + left + " = " + right + ";";
		}
		
		/** @param rfl If this argument is true, then an invokation of a setter method is created, otherwise an assignment is created. 
		 * @return String representation of an assignment or a call to a setter method. */
		public String toString(boolean rfl) {
			if(rfl){
				if(left instanceof RefEx){
					final RefEx leftEx = (RefEx)left;
					return ReflectionClassCreator.NAME_OF_CLASS +
						"."+
						ReflectionClassCreator.SET_PREFIX+
						ReflectionClassCreator.cleanTypeName(leftEx.fieldType)+
						"("+leftEx.rcObjType+".class, "+leftEx.rcObj+", \""+leftEx.field+"\", "+ right+");";					
				}else{
					return type + " " + left + " = " + right + ";";
				}				
			}else{
				return type + " " + left + " = " + right + ";";
			}
		}
		
	

	

}
