/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.logic.op;

import org.key_project.logic.Name;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.Term;
import org.key_project.logic.TermCreationException;
import org.key_project.logic.op.AbstractOperator;
import org.key_project.logic.op.Operator;
import org.key_project.logic.sort.Sort;
import org.key_project.rusty.logic.RustyDLTheory;

import org.jspecify.annotations.NonNull;

public class MutatingUpdate extends AbstractOperator implements Operator {
    public static final MutatingUpdate MUTATING_UPDATE = new MutatingUpdate();

    private MutatingUpdate() {
        super(new Name("mutating-update"), 2, true);
    }

    @Override
    public Sort sort(Sort[] sorts) {
        return RustyDLTheory.UPDATE;
    }

    @Override
    public <T extends Term> void validTopLevelException(T term) throws TermCreationException {
        super.validTopLevelException(term);

        final Sort s0 = term.sub(0).sort();
        final Sort s1 = term.sub(1).sort();

        // TODO
    }

    @Override
    public int getChildCount() {
        return 0;
    }

    @Override
    public @NonNull SyntaxElement getChild(int n) {
        throw new IndexOutOfBoundsException("Mutating updates has no children");
    }
}
