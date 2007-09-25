

package de.uka.ilkd.key.lang.clang.safe.sort.object;
import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread
import de.uka.ilkd.key.proof.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.inst.*;  //because the involved classes may be spread

/** This interface declares a tupel of two values. 
 * The first one is of type String and named key, the second one
 * is of type MemberFunction and named value
 */

public interface EntryOfStringAndMemberFunction extends java.io.Serializable {
    
    /** @return the first part of the tupel */
    String key();

    /** @return the second part of the tupel */
    MemberFunction value();
}
