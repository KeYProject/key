// @(#)$Id: JMLDataGroup.java 1.2 Tue, 17 May 2005 14:57:40 +0200 engelc $

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


package org.jmlspecs.lang;

/** A type with one element, for use in declaring "data groups".
 *  Note that there is only one equivalence class of objects of this type;
 *  that is, all objects of this type are considered .equal to each other.
 *
 * @version $Revision: 1.2 $
 * @author Gary T. Leavens, based on an idea of Rustan Leino
 */
public /*@ pure @*/ final class JMLDataGroup {

    /** Initialize this object.
     * @see #IT
     */
    /*@ private normal_behavior
      @   assignable owner;
      @   ensures owner == null;
      @*/
    private JMLDataGroup() {
    } 

    /** The only object of this type.
     */
    public static final /*@ non_null @*/ JMLDataGroup IT = new JMLDataGroup();

    /** Return this object.
     */
    public Object clone() {
        return this;
    }

    /** Test whether the given argument is a non-null object of type
     *  JMLDataGroup.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result <==> oth != null && oth instanceof JMLDataGroup;
      @*/
    public /*@ pure @*/ boolean equals(Object oth) {
        return oth != null && oth instanceof JMLDataGroup;
    } 
    
    /** Return a hash code for this object.
     */
    public /*@ pure @*/ int hashCode() {
        return 0;
    }

    /** Return a string representation of this object.
     */
    /*@ also
      @   public normal_behavior
      @     ensures \result != null
      @          && (* result is a string representation of this *);
      @*/
    public String toString() {
        return "JMLDataGroup.IT";
    }
    
}
