
package de.uka.ilkd.key.lang.clang.safe.sort.object;

import de.uka.ilkd.key.lang.clang.common.sort.object.EntryOfStringAndMemberInfo;
import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread


/** implemented by iterators of type EntryOfStringAndMemberInfo */
public interface IteratorOfEntryOfStringAndMemberInfo {

    /** @return EntryOfStringAndMemberInfo the next element of collection */
    EntryOfStringAndMemberInfo next();

    /** @return boolean true iff collection has more unseen elements */
    boolean hasNext();

}

