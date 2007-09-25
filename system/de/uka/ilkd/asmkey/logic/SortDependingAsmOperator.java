// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//

package de.uka.ilkd.asmkey.logic;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.op.SortDependingSymbol;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.logic.sort.SortDefiningSymbols;

/** This class extends the AsmOperator class and implement the SortDefiningSymbols
 * interface: it is necessary to handle the CollectionSorts.
 *
 * @author Stanislas Nanchen 
 */


public class SortDependingAsmOperator extends AsmOp implements SortDependingSymbol {

    private final Name kind;

    private final Sort sortDependingOn;

    /** Creates an sort depending asm operator.
     *
     * @param name name of operator
     * @param sort sort of term with this operator as top level operator
     * @param args count and sorts of arguments. If sort[i] is null,
     * the i-th argument of this operator may be of arbitrary sort.
     * @param boundPositions indices of subterms that bound variables.
     * @param kind name of the kind this object belongs to
     * @param sortDependingOn sort this object is depending on, this
     * is the difference between various objects of the same kind
     */
    SortDependingAsmOperator(String name,
			     Sort sort,
			     Sort[] args,
			     boolean[] boundPositions,
			     Name kind,
			     Sort sortDependingOn) {
	super (new Name(name), sort, args, boundPositions);
	this.kind = kind;
	this.sortDependingOn = sortDependingOn;
    }

    /** static function to create such an operator
     */
    public static SortDependingAsmOperator createOp(String name,
						    Sort sort,
						    Sort[] args,
						    boolean[] boundPositions,
						    Name kind,
						    Sort sortDependingOn) {
	return new SortDependingAsmOperator(name, sort, args, boundPositions, kind, sortDependingOn);
    }
    

    /**
     * @return the sort this object has been instantiated for
     */
    public Sort getSortDependingOn () {
	return sortDependingOn; 
    }


    /**
     * Compares "this" and "p"
     * @param p object to compare
     * @return true iff this and p are instances of the same kind of
     * symbol, but possibly instantiated for different sorts
     */
    public boolean isSimilar ( SortDependingSymbol p ) {
	return getKind ().equals ( p.getKind () );
    }

    /**
     * Assign a name to this term symbol, independant of concrete
     * instantiations for different sorts
     * @return the kind of term symbol this object is an instantiation
     * for
     */
    public Name getKind() {
	return kind;
    }

    /**
     * Get the instance of this term symbol defined by the given sort
     * "p_sort"
     * @return a term symbol similar to this one, or null if this
     * symbol is not defined by "p_sort"
     *
     * POSTCONDITION: result==null || (this.isSimilar(result) &&
     * result.getSortDependingOn()==p_sort)
     */
    public SortDependingSymbol getInstanceFor (SortDefiningSymbols p_sort) {
	return p_sort.lookupSymbol ( getKind () );
    }

} 
