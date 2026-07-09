/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.vm;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.Nullable;

/**
 * Matches a contiguous run of children of a parent syntax element, starting at a given child index.
 * This is the abstraction used for the active statements of a context block (phase (3) of the
 * context match): the located source element and the offset of the first active statement are
 * provided, and the run of active-statement matchers consumes one child each.
 * <p>
 * It is implemented both by the interpreter ({@link VMProgramInterpreter#matchChildrenFrom}, which
 * navigates the children with a cursor) and by the compiled matcher (which navigates them directly
 * via {@code getChild}), so the same context-block bookkeeping can drive either matcher.
 */
@FunctionalInterface
public interface ProgramChildrenMatcher {

    /**
     * Matches the children of {@code parent} starting at index {@code startChild}.
     *
     * @param parent the element whose children are to be matched
     * @param startChild the index of the first child to match against
     * @param mc the initial match conditions
     * @param services the logic services
     * @return the resulting match conditions, or {@code null} if the match fails
     */
    @Nullable
    MatchResultInfo matchChildrenFrom(SyntaxElement parent, int startChild, MatchResultInfo mc,
            LogicServices services);
}
