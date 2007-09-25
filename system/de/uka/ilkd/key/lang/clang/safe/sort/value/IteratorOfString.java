
package de.uka.ilkd.key.lang.clang.safe.sort.value;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread


/** implemented by iterators of type String */
public interface IteratorOfString {

    /** @return String the next element of collection */
    String next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}

