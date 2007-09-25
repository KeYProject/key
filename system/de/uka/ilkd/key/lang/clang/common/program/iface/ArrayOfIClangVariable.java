

package de.uka.ilkd.key.lang.clang.common.program.iface;
/** wraps an array of IClangVariables to achieve immutability */
import de.uka.ilkd.key.lang.common.program.*;
import java.util.List;

public class ArrayOfIClangVariable extends ArrayOfIProgramElement implements java.io.Serializable {

    

    /** creates an empty new IClangVariableArray
     */
    public ArrayOfIClangVariable() {
	super();
    }

    /** creates a new IClangVariableArray
     * @param arr the ProgrammElement array to wrap
     */
    public ArrayOfIClangVariable(IClangVariable[] arr) {
	super(arr);
    }


    /** creates a new IClangVariableArray with one element
     * @param el the IClangVariable that is put into the array
     */
    public ArrayOfIClangVariable(IClangVariable el) {
	super(el);
    }

    /** creates a new IClangVariableArray
     * @param list a LinkedList (order is preserved)
     */
    public ArrayOfIClangVariable(List list) {
	super(list);
    }


    /** gets the element at the specified position
     * @param pos an int describing the position
     * @return the element at pos
     */
    public final IClangVariable getIClangVariable(int pos) {
	return (IClangVariable)getIProgramElement(pos);
    }

    /** 
     * returns the last element of the array
     * @return the element at position size() - 1
     */
    public final IClangVariable lastIClangVariable() {
	return getIClangVariable(size() - 1);
    }


    /** @return size of the array */
    public int size() {
	return super.size();
    }

    

    
    
    
 
    public String toString() {
	StringBuffer sb = new StringBuffer();
	sb.append("[");
        for (int i = 0; i<size(); i++) { 
		sb.append(""+getIClangVariable(i));
		if (i<size()-1) sb.append(",");
	}
	sb.append("]");
	return sb.toString();
    }
    
}
