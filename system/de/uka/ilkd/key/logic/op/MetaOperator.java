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
 * This is the interface for MetaOperators, which are used to do complex term
 * transformation when applying a taclet. Often these transformation cannot be
 * described with the taclet scheme (or trying to do so would result in a huge
 * number of rules). The available singletons of this meta operators are kept 
 * here.
 */
public interface MetaOperator extends SortedOperator {

    /**
     * The method calculates the resulting term. The top level operator of the
     * specified term has to be this MetaOperator.
     */
    Term calculate(Term term, SVInstantiations svInst, Services services);

    public MetaOperator getParamMetaOperator(String param);

}
