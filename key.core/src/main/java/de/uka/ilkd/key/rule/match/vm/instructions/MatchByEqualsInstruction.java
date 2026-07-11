/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.match.vm.instructions;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.instruction.MatchInstruction;

import org.jspecify.annotations.Nullable;

/**
 * Matches a value-carrying leaf element by {@code equals} against the source element: the source
 * matches iff {@code pattern.equals(source)} (each element's {@code equals} compares the exact
 * class plus its payload). This mirrors the hand-written terminal matchers of the value literals
 * ({@code Literal.match} — class + boxed value), {@code TransactionStatement.match} (class +
 * transaction-type enum), and {@code ProgramElementName.match} (name identity), which recurse into
 * no children and bind no schema variables.
 *
 * <p>
 * As for the other single-position program instructions the cursor advance is performed by the
 * emitted {@code gotoNextSibling}, not here.
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
