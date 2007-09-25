// @(#)$Id: JMLListException.java 1.1 Mon, 02 May 2005 14:31:03 +0200 engelc $

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

/** Exceptions from JML List types.
 *
 * @version $Revision: 1.1 $
 * @author Gary T. Leavens
 */
//-@ immutable
//@ pure
public class JMLListException extends JMLSequenceException {

    /** Initialize this object.
     */
    public JMLListException() {
	super();
    }

    /** Initialize this object with the given detail string.
     */
    public JMLListException(String s) {
	super(s);
    }  
}
