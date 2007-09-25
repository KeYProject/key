

package de.uka.ilkd.key.lang.clang.common.program.iface;
/** wraps an array of IClangExpressions to achieve immutability */
import de.uka.ilkd.key.lang.common.program.*;
import java.util.List;

public class ArrayOfIClangExpression extends ArrayOfIProgramElement implements java.io.Serializable {

    

    /** creates an empty new IClangExpressionArray
     */
    public ArrayOfIClangExpression() {
	super();
    }

    /** creates a new IClangExpressionArray
     * @param arr the ProgrammElement array to wrap
     */
    public ArrayOfIClangExpression(IClangExpression[] arr) {
	super(arr);
    }


    /** creates a new IClangExpressionArray with one element
     * @param el the IClangExpression that is put into the array
     */
    public ArrayOfIClangExpression(IClangExpression el) {
	super(el);
    }

    /** creates a new IClangExpressionArray
     * @param list a LinkedList (order is preserved)
     */
    public ArrayOfIClangExpression(List list) {
	super(list);
    }


    /** gets the element at the specified position
     * @param pos an int describing the position
     * @return the element at pos
     */
    public final IClangExpression getIClangExpression(int pos) {
	return (IClangExpression)getIProgramElement(pos);
    }

    /** 
     * returns the last element of the array
     * @return the element at position size() - 1
     */
    public final IClangExpression lastIClangExpression() {
	return getIClangExpression(size() - 1);
    }


    /** @return size of the array */
    public int size() {
	return super.size();
    }

    

    
    
    
 
    public String toString() {
	StringBuffer sb = new StringBuffer();
	sb.append("[");
        for (int i = 0; i<size(); i++) { 
		sb.append(""+getIClangExpression(i));
		if (i<size()-1) sb.append(",");
	}
	sb.append("]");
	return sb.toString();
    }
    
}
