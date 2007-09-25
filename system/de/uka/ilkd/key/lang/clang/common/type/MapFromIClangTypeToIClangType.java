

package de.uka.ilkd.key.lang.clang.common.type;

import de.uka.ilkd.key.logic.*;  //because the involved classes may be spread
import de.uka.ilkd.key.proof.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.*;  //because the involved classes may be spread
import de.uka.ilkd.key.rule.inst.*;  //because the involved classes may be spread


/**
 * This interface has to be implemented by a Class providing a
 * persistent Map.  
 * CONVENTION: Every Class implementing MapFromIClangTypeToIClangType has to provide
 * a static final variable with the empty map  
 */
public interface MapFromIClangTypeToIClangType extends java.io.Serializable {
   
    /** adds a mapping <key,val> to the Map (old map is not modified) 
     * if key exists old entry has to be removed 
     * @return the new mapping 
     */
    MapFromIClangTypeToIClangType put(IClangType key,IClangType value);

    /** @return value of type IClangType that is mapped by key of typeIClangType */
    IClangType get(IClangType key);

    /** @return number of entries as int */
    int size();

    /** @return true iff the map includes key */
    boolean containsKey(IClangType key);

    /** @return true iff the map includes value */
    boolean containsValue(IClangType value);

    /** removes mapping (key,...) from map
     * @return the new map (the same if key is not in the map)
     */
    MapFromIClangTypeToIClangType remove(IClangType key);

    /** removes all mappings (...,value) from map
     * @return the new map (the same if value is not mapped)
     */
    MapFromIClangTypeToIClangType removeAll(IClangType value);

    /** @return iterator about all keys */
    IteratorOfIClangType keyIterator();

    /** @return iterator about all values */
    IteratorOfIClangType valueIterator();

    /** @return iterator for entries */
    IteratorOfEntryOfIClangTypeAndIClangType entryIterator();

}




    
