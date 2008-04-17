// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
// This file is part of KeY - Integrated Deductive Software Design 
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.sort.IteratorOfSort;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.SetOfSort;
import de.uka.ilkd.key.logic.sort.Sort;


/**
 * This implements a general conditional operator <tt>if (phi) (t1) (t2)</tt>
 */
public class IfThenElse extends Op {
    
    /**
     * creates the default if-else operator
     */
    IfThenElse () {
        super ( new Name ( "if-then-else" ) );
    }

    /**
     * creates an if-else operator of the given name
     */
    IfThenElse (Name name) {
        super ( name );
    }

    public boolean validTopLevel (Term term) {
        final Sort s0 = term.sub ( 0 ).sort ();
        final Sort s1 = term.sub ( 1 ).sort ();
        final Sort s2 = term.sub ( 2 ).sort ();
        
        // TODO: like in <code>ConjCond</code>, but this is really bad!!! /PR
        return term.arity () == arity ()
               && s0 == Sort.FORMULA
               && ( s1 == Sort.FORMULA ) == ( s2 == Sort.FORMULA );
    }

    public Sort sort (Term[] term) {
        final Sort s2 = term[1].sort ();
        final Sort s3 = term[2].sort ();
        if (s2 instanceof ProgramSVSort
             || s2 == AbstractMetaOperator.METASORT )
            { return s3; }
        if (s3 instanceof ProgramSVSort
             || s3 == AbstractMetaOperator.METASORT ) {
            return s2;
        } else {           
            // still a mess but a better one
            return getCommonSuperSort(s2, s3);
        }
    }
    
    private Sort getCommonSuperSort(Sort s1, Sort s2) {
        if (s1 == Sort.FORMULA) {
            assert s2 == Sort.FORMULA;
            return Sort.FORMULA;
        }
               
        if (s1.extendsTrans(s2)) return s2;
        else if (s2.extendsTrans(s1)) return s1;
        
        Sort result = Sort.ANY;
        final SetOfSort set1 = s1.extendsSorts();
        final SetOfSort set2 = s2.extendsSorts();
        
        final IteratorOfSort sort1It = set1.iterator();
        while (sort1It.hasNext()) {
            final Sort sort1 = sort1It.next();
            if (set2.contains(sort1)) {
                if (result == Sort.ANY) {
                    result = sort1;
                } else {
                    // not uniquely determinable
                    return Sort.ANY;
                }
            } 
        }        
        return result;
    }
    
    public int arity () {
        return 3;
    }   
}
