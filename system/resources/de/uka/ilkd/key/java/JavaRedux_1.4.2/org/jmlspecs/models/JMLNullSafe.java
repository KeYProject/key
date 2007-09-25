// Copyright (C) 2002 Iowa State University

// This file is part of JML

// JML is free software; you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation; either version 2, or (at your option)
// any later version.

// JML is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
// GNU General Public License for more details.

// You should have received a copy of the GNU General Public License
// along with GNU Emacs; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package org.jmlspecs.models;

/** A class with static methods that safely work with null objects.
 *
 * @version $Revision: 1.1 $
 * @author Katie Becker and Gary T. Leavens
 */
//-@ immutable
public class JMLNullSafe {

    /** No instances of this class can be created. */
    private JMLNullSafe() {}
		
    /** Test for equality of o1 and o2, allowing either to be null. */
    //@ ensures \result <==> (o1 == null ? o2 == null : o1.equals(o2));
    public static /*@ pure @*/ boolean equals(Object o1, Object o2) {
        return o1 == null ? o2 == null : o1.equals(o2);
    }

    /** Return a string representation for the argument, which may be null. */
    /*@  public normal_behavior
       @   requires o == null;
       @   assignable \nothing;
       @   ensures \result != null && \result.equals("null");
       @ also
       @   requires o != null;
       @   ensures \result != null;
       @*/
    public static String toString(Object o) {
        return o == null ? "null" : o.toString();
    }

    /** Return a hash code for the argument, which may be null. */
    /*@  public normal_behavior
       @   requires o == null;
       @   assignable \nothing;
       @   ensures \result == 0;
       @*/
    public static int hashCode(Object o) {
        return o == null ? 0 : o.hashCode();
    }
}
