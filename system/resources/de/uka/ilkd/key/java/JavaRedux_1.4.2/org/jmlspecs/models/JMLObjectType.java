// @(#)$Id: JMLObjectType.java 1.1.1.1 Mon, 09 May 2005 15:27:50 +0200 engelc $

// Copyright (C) 1998, 1999 Iowa State University

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
                                                                              

/** Objects that are containers of object references.
 * It is the intention that classes that implement JMLObjectType be
 * "containers of objects", in the sense that the user is only
 * interested in the "object references", (addresses) themselves
 * as the elements in the container. (This is in opposition to 
 * the intention of classes that implement JMLValueType.) With
 * object containers, the object references are copied in operations
 * that create new instances of the container classes, e.g., clone().
 * So there is no "deep copy" made with classes that implement
 * JMLObjectType.
 *
 * @version $Revision: 1.1.1.1 $
 * @author Gary T. Leavens
 * @author Albert L. Baker
 * @see JMLType
 */
//-@ immutable
public interface JMLObjectType extends JMLType {

    /** Return a shallow copy of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result instanceof JMLObjectType;
      @*/
    public /*@ pure @*/ Object clone();    

    /** Tell whether this object is equal to the argument, using ==
     * for comparisons to compare contained objects.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result ==>
      @        ob2 != null;
      @*/
    public /*@ pure @*/ boolean equals(Object ob2);
}
