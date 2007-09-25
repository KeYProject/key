
package de.uka.ilkd.key.lang.clang.common.type;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread


/** implemented by iterators of type IClangType */
public interface IteratorOfIClangType {

    /** @return IClangType the next element of collection */
    IClangType next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}

