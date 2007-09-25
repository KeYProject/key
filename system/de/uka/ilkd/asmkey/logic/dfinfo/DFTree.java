// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic.dfinfo;


/** DFTree is the abstract class for the tree
 * structure for storing the DFInfo's in the
 * DFInfoFactory
 *
 * @author Stanislas Nanchen
 */

abstract class DFTree {

    DFTree parent;

    static final DFTree EMPTY = new DFTree() {
	    public boolean isEmpty() { return true; }
	    public boolean isLeaf() { return false; }
	    public boolean isBranch() { return false; }
	};

    abstract public boolean isEmpty();
    abstract public boolean isLeaf();
    abstract public boolean isBranch();

    private DFTree () {
	this.parent = this;
    }

    public DFTree(DFTree parent) {
	this.parent = parent;
    }

}
