
package de.uka.ilkd.asmkey.logic;


/** implemented by iterators of type ListOfAsmProgram */
public interface IteratorOfListOfAsmProgram {

    /** @return ListOfAsmProgram the next element of collection */
    ListOfAsmProgram next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}
