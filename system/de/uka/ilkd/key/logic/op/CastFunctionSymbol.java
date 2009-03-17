// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
/*
 * Created on 13.06.2005
 */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ObjectSort;
import de.uka.ilkd.key.logic.sort.PrimitiveSort;
import de.uka.ilkd.key.logic.sort.Sort;

/**
 * This function symbol is created for casts to the depending sort. 
 * An implicit restriction belongs to the arguments sorts. We will
 * forbid side casts from reference types to primtive types as this 
 * usually indicates an error. But it should be stressed that the calculus 
 * itself would remain sound even if we would syntactically allow such kind
 * of casts.   
 */
public class CastFunctionSymbol extends SortDependingFunction {

    public static final Name NAME = new Name("cast"); 
    
    /**
     * creates an instance of a cast  
     * @param argSort the Sort of the argument (usually any)
     * @param castSort the Sort to be casted to
     */
    public CastFunctionSymbol(Sort argSort, Sort castSort) {
        super(new Name(castSort + "::" + NAME), castSort, 
                new Sort[]{ argSort }, NAME, castSort);      
    }

    
    /**
     * overrides method in {@link  de.uka.ilkd.key.logic.op.Function} and 
     * inserts an additional check disallowing which disallows side casts 
     * between primitive and reference types
     * @param at an int describing the planned sub term position of the given term
     * @param possibleSub the Term designated to become the at-th sub term 
     * @return an boolean indicating if the given term is allowed at the 
     * given position
     */  
    public boolean possibleSub(int at, Term possibleSub) {        
        final Sort castTo = getSortDependingOn(); 
        return super.possibleSub(at, possibleSub) && 
        ((castTo instanceof PrimitiveSort) != (castTo instanceof ObjectSort)) ;
    }
    
    
    /** toString */
    public String toString() {
        return "("+getSortDependingOn()+")";
    }
}
