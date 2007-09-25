// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.asmkey.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.NonRigid;
import de.uka.ilkd.key.logic.sort.Sort;

/** This class represents  a dynamic function with
 * 1 single argument that is represented by an narity
 * sort. It is used for the {@link BigOperator}.
 * @author Stanislas Nanchen 
 */
public class NArityFunction extends AsmOp implements NonRigid {

    private PrimitiveSort narity;

    private NArityFunction(Name name, Sort sort, PrimitiveSort narity) {
	super(name, sort, new Sort[] {narity});
	this.narity = narity;
    }

    public NArityFunction(Name name, Sort sort) {
	this(name, sort, PrimitiveSort.nAritySort(name));
    }

    public boolean isRigid(Term term[]) {
	return false;
    }

    public PrimitiveSort nAritySort() {
	return narity;
    }

    /** for debug only */
    public String toString() {
	return "[NArityFunction:name=" + name() + ",sort=" + sort() +"]";
    }

}
