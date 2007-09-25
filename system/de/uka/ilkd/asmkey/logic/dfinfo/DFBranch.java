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


/** DFBranch represents a branch of a DFTree and has two
 * subtree the true and the false subtree.
 *
 * @author Stanislas Nanchen
 */

class DFBranch extends DFTree {

    DFTree dffalse;
    DFTree dftrue;

    public boolean isEmpty() { return false; }
    public boolean isLeaf() { return false; }
    public boolean isBranch() { return true; }

    public DFBranch(DFTree dffalse, DFTree dftrue, DFTree parent) {
	super(parent);
	this.dffalse = dffalse;
	this.dftrue = dftrue;
    }
    
    public DFBranch(DFTree parent) {
	this(DFTree.EMPTY, DFTree.EMPTY, parent);
    }

    public void attachTree(DFTree tree, boolean dir) {
	if (dir) {
	    this.dftrue = tree;
	} else {
	    this.dffalse = tree;
	}
    }

    public void addEmptyPath(boolean[] path) {
	DFTree tree, child;
	
	if(path.length != 0) {
	    tree = this;
	    if(path[0]) {
		child = this.dftrue;
	    } else {
		child = this.dffalse;
	    }
	    for(int i = 1; i<path.length; i++) {
		if(child.isEmpty()) {
		    child = new DFBranch(tree);
		    ((DFBranch)tree).addTree(child, path[i]);
		} else if(tree.isLeaf()) {
		    // ERROR !!! should not happen.
		}
		tree = child;
		if(path[i]) {
		    child = ((DFBranch)tree).dftrue;
		} else {
		    child = ((DFBranch)tree).dffalse;
		}
	    }
	}
    }

    private void addTree(DFTree tree, boolean direction) {
	if (direction) {
	    dftrue = tree;
	} else {
	    dffalse = tree;
	}
    }

    public DFTree getFalseTree() {
	return dffalse;
    }

    public DFTree getTrueTree() {
	return dftrue;
    }

}
