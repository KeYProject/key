// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.collection;

import java.util.Iterator;


/**
 * This interface has to be implemented by a Class providing a
 * persistent Map.
 */
public interface ImmutableMap<S,T> extends java.io.Serializable {

    /** adds a mapping <key,val> to the Map (old map is not modified)
     * if key exists old entry has to be removed
     * @return the new mapping
     */
    ImmutableMap<S,T> put(S key,T value);

    /** @return value of type <T> that is mapped by key of type<S> */
    T get(S key);

    /** @return number of entries as int */
    int size();

    /** @return true iff the map is empty */
    boolean isEmpty();

    /** @return true iff the map includes key */
    boolean containsKey(S key);

    /** @return true iff the map includes value */
    boolean containsValue(T value);

    /** removes mapping (key,...) from map
     * @return the new map (the same if key is not in the map)
     */
    ImmutableMap<S,T> remove(S key);

    /** removes all mappings (...,value) from map
     * @return the new map (the same if value is not mapped)
     */
    ImmutableMap<S,T> removeAll(T value);

    /** @return iterator about all keys */
    Iterator<S> keyIterator();

    /** @return iterator about all values */
    Iterator<T> valueIterator();

    /** @return iterator for entries */
    Iterator<ImmutableMapEntry<S,T>> entryIterator();

}
