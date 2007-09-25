
package de.uka.ilkd.key.lang.clang.common.program.statement;

import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;

/** this interface has to be implemented by non-destructive lists
 * having elements  of type IStatement 
 * CONVENTION: All implementations of this interface MUST contain a
 * public static final class variable called EMPTY_LIST    
*/
public interface ListOfIStatement extends java.io.Serializable {

    /** prepends element to the list (non-destructive)
     * @param element the head of the created list
     * @return ListOfIStatement with the new element as head and this list as tail
     */
    ListOfIStatement prepend(IClangStatement element);

    /** prepends a whole list (non-destructive)
     * @param list the list to be prepended
     * @return ListOfIStatement list++this
     */

    ListOfIStatement prepend(ListOfIStatement list);

    /** prepends array (O(n))
     * @param array the array of the elements to be prepended
     * @return ListOfIStatement the new list  
     */
    ListOfIStatement prepend(IClangStatement[] array);

    /** appends element to the list (non-destructive)
     * @param element to be added at the end
     * @return ListOfIStatement with the new element at the end
     */
    ListOfIStatement append(IClangStatement element);

    /** appends a whole list (non-destructive)
     * @param list the list to be appended
     * @return ListOfIStatement this++list
     */

    ListOfIStatement append(ListOfIStatement list);

    /** appends element at end (non-destructive) (O(n))
     * @param array the array to be appended
     * @return ListOfIStatement the new list  
     */    
    ListOfIStatement append(IClangStatement[] array);
    
    /** @return IStatement the first element in list */
    IClangStatement head();

    /** @return ListOfIStatement tail of list */

    ListOfIStatement tail();

    /** @return ListOfIStatement this list without the first <code>n</code> elements  */
    ListOfIStatement take(int n);

    /**
     * Reverses this list
     */
    ListOfIStatement reverse();

    /** @return IteratorOfIStatement of this list */
    IteratorOfIStatement iterator();

    /** @return boolean is true iff. obj is in List */
    boolean contains(IClangStatement obj);

    /** @return int representing number of elements in list  */

    int size();

    /** @return true iff the list is empty */
    boolean isEmpty();

    /** removes first occurrence of obj 
     * @return new list 
     */
    ListOfIStatement removeFirst(IClangStatement obj);

    /** removes all occurrences of obj 
     * @return new list 
     */
    ListOfIStatement removeAll(IClangStatement obj);

    /**
     * Convert the list to a Java array (O(n))
     */
    IClangStatement[] toArray();    
}
