
package de.uka.ilkd.key.lang.clang.common.program.statement;

import de.uka.ilkd.key.lang.clang.common.program.iface.IClangStatement;
import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread


/** implemented by iterators of type IStatement */
public interface IteratorOfIStatement {

    /** @return IStatement the next element of collection */
    IClangStatement next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}

