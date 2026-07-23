/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.rules.matcher.compiler;

import java.util.ArrayList;
import java.util.List;

import org.key_project.logic.LogicServices;
import org.key_project.logic.SyntaxElement;
import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.prover.rules.instantiation.MatchResultInfo;
import org.key_project.prover.rules.matcher.vm.MatchProgram;

import org.jspecify.annotations.Nullable;

/**
 * The compiled matchers for a sequence of program child patterns, some of which may be list schema
 * variables (see {@link ProgramMatchPlan#listSV()}). It walks the source children with a
 * {@link ProgramChildCursor}, advancing it as it goes: a fixed child matches the one current
 * source child with its pre-compiled matcher, then the cursor steps forward one; a list-SV child
 * consumes a maximal greedy run of source children: the run extends while the current child is
 * {@linkplain ListSVMatcher#isAdmissible admissible}, the first inadmissible child is not
 * consumed, and there is no backtracking; agreement with an earlier binding is checked only after
 * the whole run has been collected ({@link ListSVMatcher#bindRun}). A cursor that is already past
 * the last child binds the empty run without moving.
 *
 * <p>
 * Whether the sequence consumed all source children is the caller's decision: it checks (or
 * deliberately ignores, e.g. for a context block whose unmatched children belong to the suffix)
 * the cursor's final position.
 */
public final class ProgramChildSequence {

    /** one pre-compiled child: either a list schema variable or a fixed child's matcher */
    private sealed interface CompiledChild {
        static CompiledChild of(ProgramMatchPlan child) {
            final SchemaVariable sv = child.listSV();
            return sv != null ? new ListSVChild(sv) : new FixedChild(child.compile());
        }
    }

    /** a list-SV child: consumes a greedy run of source children */
    private record ListSVChild(SchemaVariable listSV) implements CompiledChild {
    }

    /** a fixed child: matches exactly one source child with its pre-compiled matcher */
    private record FixedChild(MatchProgram matcher) implements CompiledChild {
    }

    private final CompiledChild[] children;
    private final ListSVMatcher listSVMatcher;
    private final boolean varArity;

    private ProgramChildSequence(CompiledChild[] children, ListSVMatcher listSVMatcher,
            boolean varArity) {
        this.children = children;
        this.listSVMatcher = listSVMatcher;
        this.varArity = varArity;
    }

    /** Pre-compiles the child plans; called once, when the enclosing plan is compiled. */
    public static ProgramChildSequence compile(ProgramMatchPlan[] plans,
            ListSVMatcher listSVMatcher) {
        final CompiledChild[] children = new CompiledChild[plans.length];
        boolean varArity = false;
        for (int i = 0; i < plans.length; i++) {
            children[i] = CompiledChild.of(plans[i]);
            varArity |= children[i] instanceof ListSVChild;
        }
        return new ProgramChildSequence(children, listSVMatcher, varArity);
    }

    /** @return whether some child is a list schema variable (consumes a run, not one child) */
    public boolean isVarArity() {
        return varArity;
    }

    /** @return the number of child patterns in this sequence */
    public int size() {
        return children.length;
    }

    /**
     * Matches the (fixed-arity) children one-to-one against consecutive children of
     * {@code parent}, starting at index {@code startChild}: child {@code i} of the pattern against
     * {@code parent.getChild(startChild + i)}. Only valid when {@link #isVarArity()} is
     * {@code false}; the caller has already checked that enough source children exist.
     */
    public @Nullable MatchResultInfo matchOneToOneFrom(SyntaxElement parent, int startChild,
            MatchResultInfo mc, LogicServices services) {
        MatchResultInfo r = mc;
        for (int i = 0; i < children.length; i++) {
            r = ((FixedChild) children[i]).matcher().match(parent.getChild(startChild + i), r,
                services);
            if (r == null) {
                return null;
            }
        }
        return r;
    }

    /**
     * Matches the children against the source, advancing {@code source} over everything consumed.
     *
     * @return the resulting match conditions, or {@code null} on failure (also when the source
     *         children run out under a fixed child pattern)
     */
    public @Nullable MatchResultInfo match(ProgramChildCursor source, MatchResultInfo mc,
            LogicServices services) {
        MatchResultInfo r = mc;
        for (final CompiledChild child : children) {
            if (child instanceof ListSVChild listChild) {
                r = matchListRun(listChild.listSV(), source, r, services);
            } else {
                final SyntaxElement sourceChild = source.getSource();
                if (sourceChild == null) {
                    return null;
                }
                r = ((FixedChild) child).matcher().match(sourceChild, r, services);
                if (r != null) {
                    source.next();
                }
            }
            if (r == null) {
                return null;
            }
        }
        return r;
    }

    /**
     * The greedy run of a list schema variable: consume source children while admissible, then
     * hand the collected run to the language for recording.
     */
    private @Nullable MatchResultInfo matchListRun(SchemaVariable listSV,
            ProgramChildCursor source, MatchResultInfo mc, LogicServices services) {
        SyntaxElement src = source.getSource();
        final List<SyntaxElement> run = new ArrayList<>();
        while (src != null) {
            if (!listSVMatcher.isAdmissible(listSV, src, mc, services)) {
                break;
            }
            run.add(src);
            source.next();
            src = source.getSource();
        }
        return listSVMatcher.bindRun(listSV, run, mc, services);
    }

    /**
     * Matches pre-compiled fixed children one-to-one against the source element's children: child
     * {@code i} of the pattern against {@code actual.getChild(i)}. The caller has already checked
     * that the child counts agree.
     */
    public static @Nullable MatchResultInfo matchOneToOne(MatchProgram[] children,
            SyntaxElement actual, MatchResultInfo mc, LogicServices services) {
        MatchResultInfo r = mc;
        for (int i = 0; i < children.length; i++) {
            r = children[i].match(actual.getChild(i), r, services);
            if (r == null) {
                return null;
            }
        }
        return r;
    }
}
