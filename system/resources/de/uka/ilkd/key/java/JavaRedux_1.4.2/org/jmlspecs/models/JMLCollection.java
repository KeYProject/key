// @(#)$Id: JMLCollection.java 1.1.1.1 Mon, 09 May 2005 15:27:50 +0200 engelc $

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

/** Common protocol of the JML model collection types.
 *
 * The use of elementType and containsNull in this specification
 * follows the ESC/Java specification of {@link java.util.Collection}.
 * That is, these ghost fields are used by the user of the object to
 * state what types of objects are allowed to be added to the collection,
 * and hence what is guaranteed to be retrieved from the collection.  They
 * are not adjusted by methods based on the content of the collection.
 *
 * @version $Revision: 1.1.1.1 $
 * @author Gary T. Leavens
 * @author Yoonsik Cheon
 * @see JMLEnumeration
 * @see JMLIterator
 */
//-@ immutable
public interface JMLCollection extends JMLType {

    /** The type of the elements in this collection.
     */
    //@ instance ghost public Object elementType;

    //@ public instance constraint elementType == \old(elementType);

    /** Whether this collection can contain null elements;
     *  think of it as "is allowed to contain null".
     */
    //@ instance ghost public boolean containsNull;

    //@ public instance constraint containsNull == \old(containsNull);


    /** Returns an Iterator over this object.
     */
    /*@ public normal_behavior
      @    ensures \fresh(\result) && \result.elementType == this.elementType;
      @    ensures !containsNull ==> !\result.returnsNull;
      @*/
    /*@ pure @*/ /*@ non_null @*/ JMLIterator iterator();

    /** Tell whether the argument is equal to one of the elements in
     * this collection, using the notion of element equality
     * appropriate for the collection.
     */
    /*@ public normal_behavior
      @    ensures_redundantly !containsNull && elem == null ==> !\result;
      @    ensures_redundantly 
      @       elem != null && !(\typeof(elem) <: elementType) ==> !\result;
      @*/    
    /*@ pure @*/ boolean has(Object elem);

    /** Tell the number of elements in this collection.
     */
    /*@ public normal_behavior
      @    ensures \result >= 0;
      @
      @ model pure public int size();
      @*/

    /*@ public normal_behavior
      @    requires size() <= Integer.MAX_VALUE;
      @    ensures \result == size();
      @*/
    /*@ pure @*/ public int int_size( );

}
