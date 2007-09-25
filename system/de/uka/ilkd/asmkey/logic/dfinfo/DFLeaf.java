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


/** DFLeaf represent a leaf of a DFTree that can contain, or not,
 * a DFInfo. we have a NULL element.
 *
 * @author Stanislas Nanchen
 */

class DFLeaf extends DFTree {

    private DFInfo info;

    public boolean isEmpty() {
	return false;
    }

    public boolean isLeaf() {
	return true;
    }

    public boolean isBranch() {
	return false;
    }

    public DFTree bud(int depth) {
	DFBranch result, temp;
	
	if (depth == 0) { return this; }
	
	result = new DFBranch(this.parent);
	temp = result;
	depth--;
	while (depth > 0) {
	    temp = new DFBranch(temp);
	    ((DFBranch)temp.parent).dffalse = temp;
	    depth--;
	}
	temp.dffalse = this;
	this.parent = temp;

	return result;
    }

    public DFInfo getDFInfo() {
	return info;
    }

    public DFLeaf(DFInfo info, DFTree parent) {
	super(parent);
	this.info = info;
    }

}
