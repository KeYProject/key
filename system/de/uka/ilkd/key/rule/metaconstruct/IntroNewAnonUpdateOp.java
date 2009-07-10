// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.OldUpdateSimplifier;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

/**
 * Creates an anonymising update for a modifies clause.
 */
public class IntroNewAnonUpdateOp extends AbstractMetaOperator {
    
    public IntroNewAnonUpdateOp() {
        super(new Name("#introNewAnonUpdate"), 3, Sort.FORMULA);
    }

    
    public Term calculate(Term term, SVInstantiations svInst, Services services) {
        Term target = term.sub(1);
        final Term updTerm = term.sub ( 2 ); 
        
        if ( !( updTerm.op () instanceof IUpdateOperator ) ) return target;

        final Update upd = Update.createUpdate ( updTerm );
        final UpdateFactory uf =
            new UpdateFactory ( services, new OldUpdateSimplifier () );
        return uf.prepend(upd, target);
    }
                
        
    public boolean isRigid(Term term) {
        return false;
    }    
}
