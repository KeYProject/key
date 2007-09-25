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

import de.uka.ilkd.asmkey.parser.env.DefaultEnvironment;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.NonRigidFunction;
import de.uka.ilkd.key.logic.op.Operator;

/** DFInfoFactory is the class that can produce and
 * manage the DFInfo. It is used in the environment.
 *
 * @author Stanislas Nanchen
 */

public class DFInfoFactory {

    private HashMapFromNameToInteger names2indices;
    private HashMapFromIntegerToName indices2names;
    private int nextIndex;
    private ListOfName names;
    private DFTree root;

    public DFInfoFactory () {
	names2indices = new HashMapFromNameToInteger();
	indices2names = new HashMapFromIntegerToName();
	nextIndex = 0;
	names = SLListOfName.EMPTY_LIST;
	root = DFTree.EMPTY;
    }

    public DFInfoFactory(DefaultEnvironment env) {
	this();
	ListOfNamed functions = env.getOperators();
	IteratorOfNamed it = functions.iterator();

	while(it.hasNext()) {
	    Operator op = (Operator) it.next();
	    if (op instanceof NonRigidFunction) {
		register(op.name());
	    }
	}
    }

    public void register(Name fun) {
	Integer integer = new Integer(nextIndex);
	nextIndex++;

	names = names.prepend(fun);
	names2indices.put(fun, integer);
	indices2names.put(integer, fun);
    }

    public DFInfo getEmptyDFInfo() throws DFException {
	return getDFInfo(SLListOfName.EMPTY_LIST);
    }

    public DFInfo getDFInfo(Name name) throws DFException {
	return getDFInfo(SLListOfName.EMPTY_LIST.prepend(name));
    }

    public DFInfo getDFInfo(ListOfName dfs) throws DFException {
	return getDFInfo(getBooleanArray(dfs));
    }
    
    private boolean[] getBooleanArray(ListOfName dfs) {
	boolean[] members = new boolean[nextIndex];
	for(int i=0; i<members.length; i++) {
	    members[i] = false;
	}

	IteratorOfName itName = dfs.iterator();
	IteratorOfName itFun;
	Name name, dyn;
	
	/* We compare each name after the other.
	 * for each name, we compare with elements of
	 * 'names' */
	while(itName.hasNext()) {
	    name = itName.next();
	    itFun = names.iterator();
	    while(itFun.hasNext()) {
		dyn = itFun.next();
		if (dyn.compareTo(name) == 0) {
		    members[names2indices.get(dyn).intValue()] = true;
		    break;
		}
	    }
	}
	return members;
    }

    DFInfo getDFInfo (boolean[] mems) throws DFException {
	/* We use the tree to verify if members is already in. if yes we
	 return the DynInfo; if no, we create a new one. */
	
	if (mems.length != 0) {
	    boolean[] members;
	    /* first we verify if member has the good length and extend it
	     * with false, if necessary. the case where the length of mems is
	     * greater is an error.
	     */
	    if (mems.length < nextIndex) {
		members = new boolean[nextIndex];
		int i;
		for(i=0;i<mems.length;i++) {
		    members[i]=mems[i];
		}
		for(;i<members.length;i++) {
		    members[i]=false;
		}
	    } else if (mems.length > nextIndex) {
		throw new DFException("mems.length > nextIndex: more boolean[] as registered functions.");
	    } else {
		members = mems;
	    }
	    
	    DFTree tree, temp;
	    boolean parentDir = false;

	    if(root.isEmpty()) {
		root = new DFBranch(root);
		root.parent = root;
	    } else if (root.isLeaf()) {
		throw new DFException("root.isLeaf(): the root cannot be a leaf.");
	    }
	    
	    tree = root;
	    for (int i=0; i<members.length; i++) {
		if (tree.isEmpty() || tree.isLeaf()) {
		    /* the tree is incomplete and we must extend it. */
		    boolean[] temparray = new boolean[members.length-i-1];
		    for(int j=0;i<temparray.length;i++) {
			temparray[j] = members[i+1+j];
		    }
		    
		    if (tree.isEmpty()) {
			/* we can simply create a new empty branch und substitute
			 * the empty node with it. */
			temp = new DFBranch(tree.parent);
		    } else {
			/* we first extends the tree where we have already
			 * dyninfo 
			 */
			temp = ((DFLeaf) tree).bud(temparray.length);
		    }
		    ((DFBranch)tree.parent).attachTree(tree, parentDir);
		    tree = temp;
		    
		    /* we then add a new path for the actual members.
		     * we can then go on and continue the wandering in
		     * in tree (avoid code duplication).
		     * (we could directly create the DFInfo and return it,
		     * consider this for an optimisation.)
		     */
		    ((DFBranch)tree).addEmptyPath(temparray);
		}
		/* we can continue to descend the tree. */
		parentDir = members[i];
		if (parentDir) {
		    tree = ((DFBranch) tree).getTrueTree();
		} else {
		    tree = ((DFBranch) tree).getFalseTree();
		}
	    }
	    /* we have descended along the tree */
	    if (tree.isEmpty()) {
		/* we must create a new DFInfo */
		DFInfo info = new DFInfo(this, members);
		DFLeaf leaf = new DFLeaf(info, tree.parent);
		((DFBranch)tree.parent).attachTree(leaf, parentDir);
		return info;
	    } else if (tree.isBranch()) {
		/* we can return the DFInfo on this leaf */
		return ((DFLeaf) tree).getDFInfo();
	    } else {
		throw new DFException("else [tree.isBranch()]: we should not come to a branch after walking down the tree.");
	    }
	} else {
	    return null;
	}
    }
    
    ListOfName getDynFunctionNames (boolean[] members) {
	ListOfName result = SLListOfName.EMPTY_LIST;
	
	for(int i=0; i<members.length; i++) {
	    if (members[i]) {
		result = result.prepend(indices2names.get(new Integer(i)));
	    }
	}
	return result;
    }

    boolean containsName (boolean[] members, Name function) {
	return members[names2indices.get(function).intValue()];
    }

}
