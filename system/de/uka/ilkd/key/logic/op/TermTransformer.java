// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
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
     * The method calculates the resulting term. The top level operator of the
     * specified term has to be this TermTransformer.
     */
    Term calculate(Term term, SVInstantiations svInst, Services services);


}
