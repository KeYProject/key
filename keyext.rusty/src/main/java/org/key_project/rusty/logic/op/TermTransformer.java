/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import org.key_project.logic.Term;
import org.key_project.logic.TerminalSyntaxElement;
import org.key_project.logic.op.Operator;
import org.key_project.logic.op.SortedOperator;
import org.key_project.rusty.Services;
import org.key_project.rusty.rule.inst.SVInstantiations;

/**
 * TermTransformer perform complex term transformation which cannot be (efficiently or at all)
 * described by taclets.
 */
public interface TermTransformer extends SortedOperator, Operator,
        /* TODO: check */ TerminalSyntaxElement {

    /**
     * initiates term transformation of <tt>term</tt>. Note the top level operator of parameter
     * <tt>term</tt> has to be <em>this</em> term transformer.
     */
    Term transform(Term term, SVInstantiations svInst, Services services);
}
