// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.util;

import java.util.Enumeration;
import java.util.Hashtable;


/**
 * Hashtable that uses identity of objects as equality relation
 * HACK: this is currently quite inefficient
 */

public class ObjectHashtable {

    private final Hashtable table;

    private final KeyContainer key;
    
    public ObjectHashtable () {
	table = new Hashtable ();
        key = new KeyContainer ( null );
    }

    private ObjectHashtable ( Hashtable p_table ) {
	table = p_table;
        key = new KeyContainer ( null );
    }

    private static class KeyContainer {
	public Object key;
	public KeyContainer   ( Object p ) {
	    key = p;
	}
	public int hashCode   () {
	    return key == null ? 0 : key.hashCode ();
	}
	public boolean equals ( Object p ) {
	    return ( p instanceof KeyContainer ) &&
		((KeyContainer)p).key == key;
	}
    }

    public Object get ( Object p_key ) {
        key.key = p_key;
	return table.get ( key );
    }

    public Object remove ( Object p_key ) {
        key.key = p_key;
	return table.remove ( key );
    }

    public Object put ( Object p_key, Object p_value ) {
	return table.put ( new KeyContainer ( p_key ), p_value );
    }
    
    public Enumeration keys () {
	return new KeyEnumeration ( table.keys () );
    }

    public boolean isEmpty () {
	return table.isEmpty ();
    }

    public void clear () {
	table.clear ();
    }

    public int size () {
        return table.size ();
    }
    
    public Object clone () {
	return new ObjectHashtable ( (Hashtable)table.clone () );
    }

    
    private static class KeyEnumeration implements Enumeration {
	private Enumeration en;
	public KeyEnumeration ( Enumeration p_en ) {
	    en = p_en;
	}
	public boolean hasMoreElements () {
	    return en.hasMoreElements ();
	}
	public Object  nextElement () {
	    return ((KeyContainer)en.nextElement ()).key;
	}
    }
    
}
