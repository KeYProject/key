// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.util.pp;

public class UnbalancedBlocksException extends IllegalStateException {
    public UnbalancedBlocksException() {
	super();
    }
    public UnbalancedBlocksException(String s) {
	super(s);
    }
}
