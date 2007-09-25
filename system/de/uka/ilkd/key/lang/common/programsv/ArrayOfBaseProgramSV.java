

package de.uka.ilkd.key.lang.common.programsv;
/** wraps an array of BaseProgramSVs to achieve immutability */
import de.uka.ilkd.key.lang.common.program.*;
import java.util.List;

public class ArrayOfBaseProgramSV extends ArrayOfIProgramElement implements java.io.Serializable {

    

    /** creates an empty new BaseProgramSVArray
     */
    public ArrayOfBaseProgramSV() {
	super();
    }

    /** creates a new BaseProgramSVArray
     * @param arr the ProgrammElement array to wrap
     */
    public ArrayOfBaseProgramSV(BaseProgramSV[] arr) {
	super(arr);
    }


    /** creates a new BaseProgramSVArray with one element
     * @param el the BaseProgramSV that is put into the array
     */
    public ArrayOfBaseProgramSV(BaseProgramSV el) {
	super(el);
    }

    /** creates a new BaseProgramSVArray
     * @param list a LinkedList (order is preserved)
     */
    public ArrayOfBaseProgramSV(List list) {
	super(list);
    }


    /** gets the element at the specified position
     * @param pos an int describing the position
     * @return the element at pos
     */
    public final BaseProgramSV getBaseProgramSV(int pos) {
	return (BaseProgramSV)getIProgramElement(pos);
    }

    /** 
     * returns the last element of the array
     * @return the element at position size() - 1
     */
    public final BaseProgramSV lastBaseProgramSV() {
	return getBaseProgramSV(size() - 1);
    }


    /** @return size of the array */
    public int size() {
	return super.size();
    }

    

    
    
    
 
    public String toString() {
	StringBuffer sb = new StringBuffer();
	sb.append("[");
        for (int i = 0; i<size(); i++) { 
		sb.append(""+getBaseProgramSV(i));
		if (i<size()-1) sb.append(",");
	}
	sb.append("]");
	return sb.toString();
    }
    
}
