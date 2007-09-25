
package de.uka.ilkd.key.lang.clang.safe.sort.value;

import de.uka.ilkd.key.lang.clang.common.sort.value.IArithmeticSort;
import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread


/** implemented by iterators of type ArithmeticSort */
public interface IteratorOfArithmeticSort {

    /** @return ArithmeticSort the next element of collection */
    IArithmeticSort next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}

