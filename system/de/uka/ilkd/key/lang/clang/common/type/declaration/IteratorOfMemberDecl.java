
package de.uka.ilkd.key.lang.clang.common.type.declaration;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread


/** implemented by iterators of type MemberDecl */
public interface IteratorOfMemberDecl {

    /** @return MemberDecl the next element of collection */
    MemberDecl next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}

