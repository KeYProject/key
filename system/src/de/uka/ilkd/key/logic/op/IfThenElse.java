// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.NullSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * This singleton class implements a general conditional operator 
 * <tt>\if (phi) \then (t1) \else (t2)</tt>.
 */
public final class IfThenElse extends AbstractOperator {
    
    public static final IfThenElse IF_THEN_ELSE = new IfThenElse();
    
        
    private IfThenElse () {
	super(new Name("if-then-else"), 3, true);
    }
    
    
    private Sort getCommonSuperSort(Sort s1, Sort s2) {
        if(s1 == Sort.FORMULA) {
            assert s2 == Sort.FORMULA: "Sorts FORMULA and "+s2+" are incompatible.";
            return Sort.FORMULA;
        } else if(s1.extendsTrans(s2)) {
            return s2;
        } else if(s2.extendsTrans(s1)) {
            return s1;
        } else if(s1 instanceof NullSort || s2 instanceof NullSort) {
            return Sort.ANY;
        } else {
            Sort result = Sort.ANY;
            final ImmutableSet<Sort> set1 = s1.extendsSorts();
            final ImmutableSet<Sort> set2 = s2.extendsSorts();
            assert set1 != null : "null for sort: " + s1;
            assert set2 != null : "null for sort: " + s2;
            
            for(final Sort sort1 : set1) {
                if(set2.contains(sort1)) {
                    if(result == Sort.ANY) {
                        result = sort1;
                    } else {
                        // not uniquely determinable
                        return Sort.ANY;
                    }
                } 
            }
            
            return result;
        }
    }        

    
    @Override
    public Sort sort(ImmutableArray<Term> terms) {
        final Sort s2 = terms.get(1).sort();
        final Sort s3 = terms.get(2).sort();
        if(s2 instanceof ProgramSVSort
             || s2 == AbstractTermTransformer.METASORT ) { 
            return s3; 
        } else if(s3 instanceof ProgramSVSort
        	  || s3 == AbstractTermTransformer.METASORT ) {
            return s2;
        } else {           
            return getCommonSuperSort(s2, s3);
        }
    }
    

    @Override
    protected boolean additionalValidTopLevel(Term term) {
        final Sort s0 = term.sub(0).sort();
        final Sort s1 = term.sub(1).sort();
        final Sort s2 = term.sub(2).sort();
        
        return s0 == Sort.FORMULA
               && (s1 == Sort.FORMULA) == (s2 == Sort.FORMULA)
               && s1 != Sort.UPDATE 
               && s2 != Sort.UPDATE;
    }
}