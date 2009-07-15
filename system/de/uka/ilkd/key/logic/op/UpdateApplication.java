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
import de.uka.ilkd.key.logic.sort.Sort;


public final class UpdateApplication extends AbstractOperator {
    
    public static final UpdateApplication UPDATE_APPLICATION 
    	= new UpdateApplication();


    private UpdateApplication () {
        super(new Name("update-application" ), 2);
    }

    
    @Override    
    public Sort sort(ArrayOfTerm terms) {
	return terms.getTerm(1).sort();
    }    
    
    
    @Override
    public boolean validTopLevel (Term term) {
        return term.arity() == arity() 
               && term.sub(0).sort() == Sort.UPDATE
               && term.varsBoundHere(0).size() == 0
               && term.varsBoundHere(1).size() == 0;
    }
    
    
    @Override
    public boolean isRigid() {
	return true;
    }
    
    
    public static int updatePos() {
	return 0;
    }
    
    
    public static Term getUpdate(Term t) {
	assert t.op() == UPDATE_APPLICATION;
	return t.sub(updatePos());
    }
    
    
    /**
     * @return the index of the subterm representing the formula/term the update
     *         is applied to
     */
    public static int targetPos() {
	return 1;
    }
    
    
    /**
     * returns the subterm representing the formula/term the update is applied to
     * @param t Term with this operator as top level operator
     */    
    public static Term getTarget(Term t) {
	assert t.op() == UPDATE_APPLICATION;
	return t.sub(targetPos());
    }
}
