

package de.uka.ilkd.key.lang.common.program;
/** wraps an array of IProgramElements to achieve immutability */
import de.uka.ilkd.key.java.*;
import java.util.List;

public class ArrayOfIProgramElement extends ArrayOfProgramElement implements java.io.Serializable {

    

    /** creates an empty new IProgramElementArray
     */
    public ArrayOfIProgramElement() {
	super();
    }

    /** creates a new IProgramElementArray
     * @param arr the ProgrammElement array to wrap
     */
    public ArrayOfIProgramElement(IProgramElement[] arr) {
	super(arr);
    }


    /** creates a new IProgramElementArray with one element
     * @param el the IProgramElement that is put into the array
     */
    public ArrayOfIProgramElement(IProgramElement el) {
	super(el);
    }

    /** creates a new IProgramElementArray
     * @param list a LinkedList (order is preserved)
     */
    public ArrayOfIProgramElement(List list) {
	super(list);
    }


    /** gets the element at the specified position
     * @param pos an int describing the position
     * @return the element at pos
     */
    public final IProgramElement getIProgramElement(int pos) {
	return (IProgramElement)getProgramElement(pos);
    }

    /** 
     * returns the last element of the array
     * @return the element at position size() - 1
     */
    public final IProgramElement lastIProgramElement() {
	return getIProgramElement(size() - 1);
    }


    /** @return size of the array */
    public int size() {
	return super.size();
    }

    

    
    
    
 
    public String toString() {
	StringBuffer sb = new StringBuffer();
	sb.append("[");
        for (int i = 0; i<size(); i++) { 
		sb.append(""+getIProgramElement(i));
		if (i<size()-1) sb.append(",");
	}
	sb.append("]");
	return sb.toString();
    }
    
}
