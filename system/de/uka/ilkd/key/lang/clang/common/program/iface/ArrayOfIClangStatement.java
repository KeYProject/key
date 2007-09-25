

package de.uka.ilkd.key.lang.clang.common.program.iface;
/** wraps an array of IClangStatements to achieve immutability */
import de.uka.ilkd.key.lang.common.program.*;
import java.util.List;

public class ArrayOfIClangStatement extends ArrayOfIProgramElement implements java.io.Serializable {

    

    /** creates an empty new IClangStatementArray
     */
    public ArrayOfIClangStatement() {
	super();
    }

    /** creates a new IClangStatementArray
     * @param arr the ProgrammElement array to wrap
     */
    public ArrayOfIClangStatement(IClangStatement[] arr) {
	super(arr);
    }


    /** creates a new IClangStatementArray with one element
     * @param el the IClangStatement that is put into the array
     */
    public ArrayOfIClangStatement(IClangStatement el) {
	super(el);
    }

    /** creates a new IClangStatementArray
     * @param list a LinkedList (order is preserved)
     */
    public ArrayOfIClangStatement(List list) {
	super(list);
    }


    /** gets the element at the specified position
     * @param pos an int describing the position
     * @return the element at pos
     */
    public final IClangStatement getIClangStatement(int pos) {
	return (IClangStatement)getIProgramElement(pos);
    }

    /** 
     * returns the last element of the array
     * @return the element at position size() - 1
     */
    public final IClangStatement lastIClangStatement() {
	return getIClangStatement(size() - 1);
    }


    /** @return size of the array */
    public int size() {
	return super.size();
    }

    

    
    
    
 
    public String toString() {
	StringBuffer sb = new StringBuffer();
	sb.append("[");
        for (int i = 0; i<size(); i++) { 
		sb.append(""+getIClangStatement(i));
		if (i<size()-1) sb.append(",");
	}
	sb.append("]");
	return sb.toString();
    }
    
}
