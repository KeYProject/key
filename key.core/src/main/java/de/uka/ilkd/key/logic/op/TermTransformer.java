/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.op;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/**
 * TermTransformer perform complex term transformation which cannot be (efficiently or at all)
 * described by taclets.
 */
public interface TermTransformer extends SortedOperator {

    /**
     * initiates term transformation of <tt>term</tt>. Note the top level operator of of parameter
     * <tt>term</tt> has to be <em>this</em> term transformer.
     */
    Term transform(Term term, SVInstantiations svInst, Services services);
}
