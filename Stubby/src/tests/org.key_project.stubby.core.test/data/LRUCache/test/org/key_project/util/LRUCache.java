package org.key_project.util;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * Simple realisation of an LRU cache.
 */
public class LRUCache<K,V> extends LinkedHashMap<K,V> {

    /**
     * 
     */
    private static final long serialVersionUID = 4962274836567079680L;
    /** maximal cache size */
    private final int maxEntries;

    /**
     * creates a new LRU cached with maxEntires slots
     */
    public LRUCache(int maxEntries) {
	super(maxEntries + 1, 1.0F, true);
	this.maxEntries = maxEntries;
    }

    /**
     * removes the eldest entry, i.e. the least recently used one
     */
    @Override
    protected boolean removeEldestEntry(Map.Entry<K,V> eldest) {
	return size() > maxEntries;
    }
}