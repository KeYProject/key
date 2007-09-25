
package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread


/** implemented by iterators of type MemberFunction */
public interface IteratorOfMemberFunction {

    /** @return MemberFunction the next element of collection */
    MemberFunction next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}

