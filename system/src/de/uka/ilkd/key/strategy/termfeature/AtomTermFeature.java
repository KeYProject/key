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

package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.*;

public class AtomTermFeature extends BinaryTermFeature {

    public static final TermFeature INSTANCE = new AtomTermFeature ();
    
    private AtomTermFeature () {}
    
    protected boolean filter(Term term, Services services) {
        final Operator op = term.op ();
        return ! ( op instanceof Junctor
                   || op == Equality.EQV
                   || op instanceof IfThenElse
                   || op instanceof Quantifier );
    }
    
}