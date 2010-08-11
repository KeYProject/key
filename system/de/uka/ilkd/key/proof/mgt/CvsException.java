// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//



// CvsException.java
// $Id: CvsException.java 1.3 Mon, 28 Feb 2005 14:52:06 +0100 andreas $
// (c) COPYRIGHT MIT and INRIA, 1996.
// Please first read the full copyright statement in file COPYRIGHT.html

package de.uka.ilkd.key.proof.mgt;

/**
 * This exception is used whenever an abnormal situation in CVS processing
 * is encountered.
 */

public class CvsException extends Exception {

    CvsException (String msg) {
	super (msg) ;
    }
}

   
	
