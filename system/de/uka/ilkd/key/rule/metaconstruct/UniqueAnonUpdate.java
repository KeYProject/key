// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.op.AbstractMetaOperator;
import de.uka.ilkd.key.logic.op.AnonymousUpdate;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

public class UniqueAnonUpdate extends AbstractMetaOperator {

    public UniqueAnonUpdate() {
        super(new Name("#uniqueAnonUpdate"), 1);
    }
    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        return TermFactory.DEFAULT.createAnonymousUpdateTerm(
                AnonymousUpdate.getNewAnonymousOperator(), term.sub(0));
    }

    public Sort sort(){
        return Sort.FORMULA;
    }
    
    /** Unlike other meta operators this one returns a formula
     * not a term.
     */
    public Sort sort(Term[] term) {
        return Sort.FORMULA;
    }
    
}
