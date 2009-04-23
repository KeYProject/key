// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.util;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Simple realisation of an LRU cache.
 */
public class LRUCache<K,V> extends LinkedHashMap<K,V> {

    /** maximal cache size */
    private final int maxEntries;

    /**
     * creates a new LRU cached with maxEntires slots
     */
    public LRUCache(int maxEntries) {
	super((int)(maxEntries*1.01), 1.0F, true);
	this.maxEntries = maxEntries;
    }

    /**
     * removes the eldest entry, i.e. the least recently used one
     */
    protected boolean removeEldestEntry(Map.Entry<K,V> eldest) {
	return size() > maxEntries;
    }
}
