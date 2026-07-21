/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm.instruction;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.Nullable;

/**
 * Matches a value-carrying leaf element by {@code equals} against the source element: the source
 * matches iff {@code pattern.equals(source)}, where the element's {@code equals} is expected to
 * compare the exact class plus its payload (a literal's value, a name, an enum constant, ...).
 * Complements {@link MatchIdentityInstruction} for leaves whose instances are not canonicalized,
 * so reference identity would be too strict. It recurses into no children and binds no schema
 * variables.
 *
 * <p>
 * As for the other single-position instructions the cursor advance is performed by the emitted
 * {@code gotoNextSibling}, not here.
 */
public final class MatchByEqualsInstruction implements MatchInstruction {

    private final SyntaxElement pattern;

    public MatchByEqualsInstruction(SyntaxElement pattern) {
        this.pattern = pattern;
    }

    @Override
    public @Nullable MatchResultInfo match(SyntaxElement actualElement,
            MatchResultInfo matchConditions, LogicServices services) {
        return pattern.equals(actualElement) ? matchConditions : null;
    }
}
