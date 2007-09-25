

package de.uka.ilkd.key.lang.clang.common.type.declaration;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread
import de.uka.ilkd.key.proof.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.inst.*;  //because the involved classes may be spread


/**
 * This interface has to be implemented by a Class providing a
 * persistent Map.  
 * CONVENTION: Every Class implementing MapFromStringToStructDecl has to provide
 * a static final variable with the empty map  
 */
public interface MapFromStringToStructDecl extends java.io.Serializable {
   
    /** adds a mapping <key,val> to the Map (old map is not modified) 
     * if key exists old entry has to be removed 
     * @return the new mapping 
     */
    MapFromStringToStructDecl put(String key,StructDecl value);

    /** @return value of type StructDecl that is mapped by key of typeString */
    StructDecl get(String key);

    /** @return number of entries as int */
    int size();

    /** @return true iff the map includes key */
    boolean containsKey(String key);

    /** @return true iff the map includes value */
    boolean containsValue(StructDecl value);

    /** removes mapping (key,...) from map
     * @return the new map (the same if key is not in the map)
     */
    MapFromStringToStructDecl remove(String key);

    /** removes all mappings (...,value) from map
     * @return the new map (the same if value is not mapped)
     */
    MapFromStringToStructDecl removeAll(StructDecl value);

    /** @return iterator about all keys */
    IteratorOfString keyIterator();

    /** @return iterator about all values */
    IteratorOfStructDecl valueIterator();

    /** @return iterator for entries */
    IteratorOfEntryOfStringAndStructDecl entryIterator();

}




    
