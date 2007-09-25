
package de.uka.ilkd.key.lang.clang.common.sort.object;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread


/** implemented by iterators of type MemberInfo */
public interface IteratorOfMemberInfo {

    /** @return MemberInfo the next element of collection */
    MemberInfo next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}

