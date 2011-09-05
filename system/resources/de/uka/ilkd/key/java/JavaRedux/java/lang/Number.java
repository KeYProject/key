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
// along with JML; see the file COPYING.  If not, write to
// the Free Software Foundation, 675 Mass Ave, Cambridge, MA 02139, USA.

package java.lang;

/** JML's specification of java.lang.Number.
 * Taken from jmlspecs repository and modified to be usable with KeY.
 * @version $Revision: 1388 $ KeY
 * @author Brandon Shilling
 * @author Gary T. Leavens
 * @author Daniel Bruns
 */
public abstract class Number implements java.io.Serializable {

    /*@ public normal_behavior
      @   ensures true;
      @*/
    public /*@ pure @*/ Number();

    public abstract /*@ pure @*/ int intValue();

    public abstract /*@ pure @*/ long longValue();
    
    public abstract /*@ pure @*/ float floatValue();

    public abstract /*@ pure @*/ double doubleValue();

    public /*@ pure @*/ byte byteValue();

    public /*@ pure @*/ short shortValue();
}
