// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.logic.sort;

import de.uka.ilkd.asmkey.logic.SortDependingAsmOperator;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.op.SortDependingSymbol;
import de.uka.ilkd.key.logic.sort.AbstractCollectionSort;
import de.uka.ilkd.key.logic.sort.AbstractNonCollectionSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;

public class SequenceSort extends AbstractCollectionSort 
    implements SortDefiningSymbols {
    
    
    /** creates a Sort (with a new equality symbol for this sort) */
    protected SequenceSort(de.uka.ilkd.key.logic.sort.Sort elemSort) {
	super("[" + elemSort.name() + "]",elemSort);
    }

    /**
     * @return an object of this class with elementSort().equals(p),
     * or null if such an object cannot be constructed (as p is an
     * incompatible sort)
     */
    public Sort cloneFor ( Sort p ) {
	if ( p instanceof AbstractNonCollectionSort )
	    return ((AbstractNonCollectionSort)p).getSequenceSort ();
	else
	    return null;
    }


    /**
     * Create the symbols defined by this sort, insert them into the
     * namespace "p_func_ns"
     * @param p_func_ns Namespace to which functions and predicates
     * should be added to
     */
    public void createSymbols ( Namespace p_func_ns, Namespace sort_ns ) {
	//KeYMediator mediator = Main.getInstance().mediator();	
	Sort el_sort = this.elementSort();

	createOperator("cons", this, new Sort[] { el_sort, this }, p_func_ns);
	//((AsmNotationInfo) mediator.getNotationInfo()).putAsmNotation(op, AsmNotation.sequence());
	
	createOperator("nil", this, new Sort[0], p_func_ns);
	//((AsmNotationInfo) mediator.getNotationInfo()).putAsmNotation(op, AsmNotation.empty_sequence());
	
	
	createOperator("head", el_sort, new Sort[] { this }, p_func_ns);

	createOperator("tail", this, new Sort[] { this }, p_func_ns);

	createOperator("isNil", Sort.FORMULA, new Sort[] { this }, p_func_ns);

	createOperator("member", Sort.FORMULA, new Sort[] { el_sort, this }, p_func_ns);

	createOperator("append", Sort.FORMULA, new Sort[] { this, this, this }, p_func_ns);
	
	createOperator("select", Sort.FORMULA, new Sort[] { el_sort, this, this }, p_func_ns);

	createOperator("perm", Sort.FORMULA, new Sort[] {this, this}, p_func_ns);
    }

    /**
     * Lookup the symbol of kind "p_name", which is a sort
     * independent identifier for this symbol
     * @return Symbol with (kind) name "p_name"
     * ("ret.getKind().equals(p_name)"), null if no such object exists
     */
    public SortDependingSymbol lookupSymbol  ( Name      p_name ) {
	return definedSymbols.get(p_name);
    }
    
    /** method to create a particular operator, it adds at the same time in the p_func_ns. */
    private SortDependingAsmOperator createOperator(String name_p,
						    Sort valueSort,
						    Sort[] argSorts,
						    Namespace p_func_ns) {
	SortDependingAsmOperator op;

	/*boolean boundPos[] = new boolean[argSorts.length];
	for(int i = 0; i<boundPos.length; i++) {
	    boundPos[i] = false;
	    }*/

	String opName = name_p + "_" + this.elementSort().name();
	Name kind = new Name("sequence::" + name_p);

	op = SortDependingAsmOperator.createOp(opName,
					       valueSort,
					       argSorts,
					       null,
					       kind,
					       this);
	definedSymbols = definedSymbols.put(kind, op);
	p_func_ns.add(op);
 
	return op;
    }

}
