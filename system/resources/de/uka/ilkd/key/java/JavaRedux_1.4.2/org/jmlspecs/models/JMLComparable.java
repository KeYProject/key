// @(#) $Id: JMLComparable.java 1.1.1.1 Mon, 09 May 2005 15:27:50 +0200 engelc $

// Copyright (C) 2001 Iowa State University

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
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package org.jmlspecs.models;


/** JMLTypes with an compareTo operation, as in {@link java.lang.Comparable}.
 *
 * @version $Revision: 1.1.1.1 $
 * @author Gary T. Leavens
 * @see java.lang.Comparable
 */
//-@ immutable
public /*@ pure @*/ interface JMLComparable
    extends JMLType, Comparable {

    /** Compare this to o, returning a comparison code.
     *  @param o the object this is compared to.
     *  @exception ClassCastException when o doesn't have an appropriate type.
     */
    /*@ also
      @   public behavior
      @     requires o != null;
      @     signals (ClassCastException) ;
      @*/
    public int compareTo(Object o) throws ClassCastException;

}

