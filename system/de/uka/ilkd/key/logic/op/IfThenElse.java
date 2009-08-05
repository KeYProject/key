// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.ArrayOfTerm;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.SetOfSort;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * This implements a general conditional operator <tt>if (phi) (t1) (t2)</tt>
 */
public final class IfThenElse extends AbstractOperator {
    
    public static final IfThenElse IF_THEN_ELSE = new IfThenElse ();
    
        
    private IfThenElse () {
	super(new Name("if-then-else"), 3, true);
    }
    
    
    private Sort getCommonSuperSort(Sort s1, Sort s2) {
        if(s1 == Sort.FORMULA) {
            assert s2 == Sort.FORMULA;
            return Sort.FORMULA;
        } else if(s1.extendsTrans(s2)) {
            return s2;
        } else if(s2.extendsTrans(s1)) {
            return s1;
        } else if(s1 == Sort.NULL || s2 == Sort.NULL) {
            return Sort.ANY;
        } else {
            Sort result = Sort.ANY;
            final SetOfSort set1 = s1.extendsSorts();
            final SetOfSort set2 = s2.extendsSorts();
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
    public Sort sort(ArrayOfTerm terms) {
        final Sort s2 = terms.getTerm(1).sort ();
        final Sort s3 = terms.getTerm(2).sort ();
        if(s2 instanceof ProgramSVSort
             || s2 == AbstractMetaOperator.METASORT ) { 
            return s3; 
        } else if(s3 instanceof ProgramSVSort
        	  || s3 == AbstractMetaOperator.METASORT ) {
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
