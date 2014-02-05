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


package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * TermTransformer perform complex term transformation which cannot be
 * (efficiently or at all) described by taclets.
 */
public interface TermTransformer extends SortedOperator {

    /**
     * initiates term transformation of <tt>term</tt>. Note the top level operator of
     * of parameter <tt>term</tt> has to be <em>this</em> term transformer.
     */
    Term transform(Term term, SVInstantiations svInst, Services services);
}
