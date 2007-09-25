
package de.uka.ilkd.key.lang.clang.common.type.declaration;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread


/** implemented by iterators of type ArithmeticTypeDecl */
public interface IteratorOfArithmeticTypeDecl {

    /** @return ArithmeticTypeDecl the next element of collection */
    ArithmeticTypeDecl next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}

