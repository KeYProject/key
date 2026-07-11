/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.List;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;

import org.jspecify.annotations.Nullable;

/**
 * Language SPI (service provider interface) for matching <em>list program schema variables</em> —
 * schema variables such as
 * {@code #slist} that stand for a run of consecutive statements or expressions rather than exactly
 * one. What a run may contain is language-specific: each front-end decides for itself which
 * program elements a schema variable may stand for, and stores the matched run in its own typed
 * instantiation entry.
 *
 * <p>
 * The framework owns the matching itself ({@link ProgramChildSequence}): it walks the source
 * children and greedily extends the run while {@link #isAdmissible} holds — the first inadmissible
 * child is not consumed, and there is no backtracking. The language plugs in only the two
 * judgements below.
 */
public interface ListSVMatcher {

    /**
     * @param listSV the list schema variable being matched
     * @param element the source child the greedy run would consume next
     * @param mc the match conditions found so far (a language may consult its instantiations, e.g.
     *        for the execution context in which the element occurs)
     * @param services the logic services
     * @return whether {@code element} may become part of {@code listSV}'s run
     */
    boolean isAdmissible(SchemaVariable listSV, SyntaxElement element, MatchResultInfo mc,
            LogicServices services);

    /**
     * Records the maximal run collected for {@code listSV}, or — if the schema variable is already
     * bound — succeeds without change exactly when the existing binding equals the run.
     *
     * @param listSV the list schema variable being matched
     * @param run the consecutive source children the greedy run consumed (possibly empty)
     * @param mc the match conditions found so far
     * @param services the logic services
     * @return the resulting match conditions, or {@code null} on failure (a conflicting earlier
     *         binding, or a language-specific veto)
     */
    @Nullable
    MatchResultInfo bindRun(SchemaVariable listSV, List<? extends SyntaxElement> run,
            MatchResultInfo mc, LogicServices services);
}
