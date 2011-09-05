// Copyright (C) 2004 Iowa State University

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

package java.util;

/** JML's specification of ArrayList.
 *  Taken from jmlspecs repository and modified to be useable with KeY.
 *  @author Ajani Thomas
 *  @author Gary T. Leavens
 *  @author Daniel Bruns
 */
public class ArrayList /*extends AbstractList*/
    implements List, /*RandomAccess,*/ Cloneable, java.io.Serializable
{

    /*@ pure @*/ public ArrayList(int initialCapacity) throws IllegalArgumentException;

    /*@ pure @*/ public ArrayList();

    /*@ pure @*/ public ArrayList(Collection c) throws NullPointerException;

    public void trimToSize();

    public void ensureCapacity(int minCapacity);

    // specification inherited from List
    public /*@ pure @*/ int size();
    // specification inherited from List
    public /*@ pure @*/ boolean isEmpty();

    // specification inherited from List
    public /*@ pure @*/ boolean contains(/*@nullable*/Object elem);

    // specification inherited from List
    public /*@ pure @*/ int indexOf(Object elem);

    // specification inherited from List
    public /*@ pure @*/ int lastIndexOf(Object elem);

    public /*@ pure @*/ Object clone();

    // specification inherited from List
    public /*@ pure @*/ Object[] toArray();

    // specification inherited from List
    public Object[] toArray(Object[] a);

    // specification inherited from List
    public /*@ pure @*/ Object get(int index);

    // specification inherited from List
    public Object set(int index, Object element);

    // specification inherited from List
    public boolean add(/*@nullable*/Object o);

    // specification inherited from List
    public void add(int index, Object element);

    // specification inherited from List
    public Object remove(int index);

    // specification inherited from List
    public void clear();

    // specification inherited from List
    public boolean addAll(Collection c);

    // specification inherited from List
    public boolean addAll(int index, Collection c);

    // specification inherited from AbstractList
//    protected void removeRange(int fromIndex, int toIndex);
} 
