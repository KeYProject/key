// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.storage;


/**
 * This exception is thrown when a problem occurs
 * in the storage manager, like file not present, etc...
 */
public class StorageException extends Exception {

    public StorageException(String s) {
	super(s);
    }

    public StorageException(Exception e) {
	super(e);
    }
    
}
