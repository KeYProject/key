/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule.tacletbuilder;

import org.key_project.logic.Term;
import org.key_project.rusty.rule.BoundUniquenessChecker;
import org.key_project.rusty.rule.FindTaclet;

public abstract class FindTacletBuilder<T extends FindTaclet> extends TacletBuilder<T> {
    protected Term find = null;

    /**
     * checks that a SchemaVariable that is used to match pure variables (this means bound
     * variables) occurs at most once in a quantifier of the assumes and finds and throws an
     * exception otherwise
     */
    protected void checkBoundInIfAndFind() {
        final BoundUniquenessChecker ch = new BoundUniquenessChecker(getFind(), ifSequent());
        if (!ch.correct()) {
            throw new TacletBuilder.TacletBuilderException(this,
                "A bound SchemaVariable variables occurs both " + "in assumes and find clauses.");
        }
    }

    /*
     * Get the `find' term. This could be a term or a formula for a RewriteTaclet, but only a
     * formula for an Antec/Succ Taclet.
     */
    public Term getFind() {
        return find;
    }

}
