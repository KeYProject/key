// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 



package de.uka.ilkd.key.strategy.termfeature;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.strategy.termProjection.TermBuffer;

/**
 * Term feature for testing equality of two terms. The feature returns zero iff
 * it is invoked on a term that is equal to the current value of
 * <code>pattern</code>.
 * 
 * NB: it is not possible to use general <code>ProjectionToTerm</code> here,
 * because the information necessary to evaluate a <code>ProjectionToTerm</code>
 * is not available in a term feature
 */
public class EqTermFeature extends BinaryTermFeature {

    private final TermBuffer pattern;

    public static TermFeature create(TermBuffer pattern) {
        return new EqTermFeature ( pattern );
    }
    
    private EqTermFeature(TermBuffer pattern) {
        this.pattern = pattern;
    }
    
    protected boolean filter(Term term) {
        return term.equals ( pattern.getContent () );
    }
}
