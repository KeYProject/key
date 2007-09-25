// @(#)$Id: JMLIterator.java 1.1 Mon, 02 May 2005 14:31:03 +0200 engelc $

// Copyright (C) 1998, 1999, 2002 Iowa State University

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

import java.util.Iterator;

/** A combination of JMLType and java.util.Iterator.
 *  None of these support the remove operation.
 * @version $Revision: 1.1 $
 * @author Gary T. Leavens
 * @see JMLEnumeration
 * @see JMLEnumerationToIterator
 */
//-@ immutable
public interface JMLIterator extends Iterator, JMLType {

    /** Return a clone of this iterator.
     */
    Object clone();

    /*@ also
      @   assignable \nothing;
      @*/
    /*@ pure @*/ boolean hasNext();

    //@ public instance represents moreElements <- hasNext();
}
