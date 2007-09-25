// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.util;

import java.util.Collection;
import java.util.Iterator;

import de.uka.ilkd.key.logic.IteratorOfNamed;
import de.uka.ilkd.key.logic.Named;


/** Static methods to print collections.
 *
 * @see ArrayUtil
 * @author Hubert Schmid
 */

public final class CollectionUtil {

    private CollectionUtil() {}
    
    /** Default infix for {@link #toString(Collection)}. */
    protected static final String DEFAULT_INFIX = ",";


    /** Returns a string representing all elements in the collection.
     * The elements are separated with <tt>infix</tt>. */
    public static String toString(Collection c, String infix) {
        if (c == null) {
            return "null";
        } else if (c.size() == 0) {
            return "[]";
        } else {
            StringBuffer sb = new StringBuffer('[');
            Iterator i = c.iterator();
            sb.append(i.next());
            while (i.hasNext()) {
                sb.append(infix).append(i.next());
            }
            sb.append(']');
            return sb.toString();
        }
    }

    /** return @{link #toString(Collection, String) toString(array,
     * ",")} */
    public static String toString(Collection c) {
        return toString(c, DEFAULT_INFIX);
    }

    public static IteratorOfNamed convertToIteratorOfNamed(Iterator it) {
	return new NamedIterator(it);
    }
    
    private static class NamedIterator implements IteratorOfNamed {
	Iterator it;

	public NamedIterator(Iterator it) {
	    this.it = it;
	}
	
	public Named next() {
	    return (Named) it.next();
	}

	public boolean hasNext() {
	    return it.hasNext();
	}
    }

}
