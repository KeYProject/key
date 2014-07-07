package de.uka.ilkd.key.testgen;

/** Reference expression 
 * @author gladisch
*/
public class RefEx {
	public String rcObjType;
	public String rcObj;
	public String fieldType;
	public String field;

	/** Example: rcObj.field, where rcObjType is the type of rcObj.
	 *  The prefix "rc" stands for receiver. 
	 */	
	public RefEx(String rcObjType, String rcObj, String fieldType, String field){
		this.rcObjType = rcObjType;
		this.rcObj = rcObj;
		this.fieldType = fieldType;
		this.field = field;
	}
	
	@Override
	public String toString() {
		if(rcObjType!=null && rcObjType!=""){
			return "(("+rcObjType+")"+ rcObj+")."+field;
		}
		return rcObj+"."+field;
	}
}
