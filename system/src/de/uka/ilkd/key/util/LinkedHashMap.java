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

package de.uka.ilkd.key.util;

import java.util.Iterator;

public class LinkedHashMap<K, V>
	extends java.util.LinkedHashMap<K, V> {

    /**
     * 
     */
    private static final long serialVersionUID = -6216276580053259582L;
    
    
    public LinkedHashMap() {
	super();
    }
    
    
    public LinkedHashMap(K key, V value) {
	super();
	put(key, value);
    }
    
    
    public LinkedHashMap(K[] keys, V[] values) {
	super();
	putAll(keys, values);
    }
    
    
    public LinkedHashMap(Iterable<K> keys, Iterable<V> values) {
	super();
	putAll(keys, values);
    }
    
    
    public void putAll(K[] keys, V[]vals) {
	for (int i = 0; i < keys.length; i++) {
	    if (i < vals.length) {
		put(keys[i], vals[i]);
	    } else {
		put(keys[i], null);
	    }
	}
    }

    
    public void putAll(Iterable<K> keys, Iterable<V> vals) {
	Iterator<V> itVals = vals.iterator();
	for (K key : keys) {
	    if (itVals.hasNext()) {
		put(key, itVals.next());
	    } else {
		put(key, null);
	    }
	}
    }
    
}