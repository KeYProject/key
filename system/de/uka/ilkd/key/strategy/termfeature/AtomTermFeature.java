// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IfThenElse;
import de.uka.ilkd.key.logic.op.Junctor;
import de.uka.ilkd.key.logic.op.Op;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.Quantifier;

public class AtomTermFeature extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new AtomTermFeature ();
    
    private AtomTermFeature () {}
    
    protected boolean filter(Term term) {
        final Operator op = term.op ();
        return ! ( op instanceof Junctor
                   || op == Op.EQV
                   || op instanceof IfThenElse
                   || op instanceof Quantifier );
    }
    
}
