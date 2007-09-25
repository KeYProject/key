package de.uka.ilkd.key.util;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Simple realisation of an LRU cache.
 */
public class LRUCache extends LinkedHashMap {

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
    protected boolean removeEldestEntry(Map.Entry eldest) {
	return size() > maxEntries;
    }
}
