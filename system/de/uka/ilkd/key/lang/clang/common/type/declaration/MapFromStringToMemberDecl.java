

package de.uka.ilkd.key.lang.clang.common.type.declaration;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread
import de.uka.ilkd.key.proof.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.inst.*;  //because the involved classes may be spread


/**
 * This interface has to be implemented by a Class providing a
 * persistent Map.  
 * CONVENTION: Every Class implementing MapFromStringToMemberDecl has to provide
 * a static final variable with the empty map  
 */
public interface MapFromStringToMemberDecl extends java.io.Serializable {
   
    /** adds a mapping <key,val> to the Map (old map is not modified) 
     * if key exists old entry has to be removed 
     * @return the new mapping 
     */
    MapFromStringToMemberDecl put(String key,MemberDecl value);

    /** @return value of type MemberDecl that is mapped by key of typeString */
    MemberDecl get(String key);

    /** @return number of entries as int */
    int size();

    /** @return true iff the map includes key */
    boolean containsKey(String key);

    /** @return true iff the map includes value */
    boolean containsValue(MemberDecl value);

    /** removes mapping (key,...) from map
     * @return the new map (the same if key is not in the map)
     */
    MapFromStringToMemberDecl remove(String key);

    /** removes all mappings (...,value) from map
     * @return the new map (the same if value is not mapped)
     */
    MapFromStringToMemberDecl removeAll(MemberDecl value);

    /** @return iterator about all keys */
    IteratorOfString keyIterator();

    /** @return iterator about all values */
    IteratorOfMemberDecl valueIterator();

    /** @return iterator for entries */
    IteratorOfEntryOfStringAndMemberDecl entryIterator();

}




    
