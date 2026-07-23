/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast;

import java.util.List;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.ast.reference.IExecutionContext;
import de.uka.ilkd.key.java.ast.statement.MethodFrame;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramPrefix;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

import org.key_project.prover.rules.matcher.vm.ProgramChildrenMatcher;
import org.key_project.util.collection.ImmutableArray;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.Nullable;

/**
 * In the DL-formulae description of Taclets the program part can have the following form
 * {@code < pi
 * alpha;...; omega > Phi} where {@code pi} is a prefix consisting of open brackets, {@code try}'s
 * and so on and
 * omega is the rest of the program. Between the prefix {@code pi} and the postfix {@code omega}
 * there can stand an
 * arbitrary program. This pattern is realized using this class.
 */

public class ContextStatementBlock extends StatementBlock {


    /**
     * the last execution context of the context term
     */
    private final IExecutionContext executionContext;

    public ContextStatementBlock(Statement s, IExecutionContext executionContext) {
        super(s);
        this.executionContext = executionContext;
    }

    public ContextStatementBlock(Statement[] body, IExecutionContext executionContext) {
        super(body);
        this.executionContext = executionContext;
    }

    public ContextStatementBlock(
            PositionInfo pi, List<Comment> c,
            ImmutableArray<? extends Statement> body,
            IExecutionContext execContext) {
        super(pi, c, body, ImmutableList.nil());
        this.executionContext = execContext;
    }

    public IExecutionContext getExecutionContext() {
        return executionContext;
    }

    /**
     * Returns the number of children of this node.
     *
     * @return an int giving the number of children of this node
     */

    public int getChildCount() {
        int count = 0;
        if (executionContext != null) {
            count++;
        }
        count += super.getChildCount();
        return count;
    }

    /**
     * Returns the child at the specified index in this node's "virtual" child array
     *
     * @param index
     *        an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException
     *            if <tt>index</tt> is out of bounds
     */
    public ProgramElement getChildAt(int index) {
        if (executionContext != null) {
            if (index == 0) {
                return executionContext;
            }
            index--;
        }
        return super.getChildAt(index);
    }

    /**
     * calls the corresponding method of a visitor in order to perform some action/transformation on
     * this element
     *
     * @param v
     *        the Visitor
     */
    public void visit(Visitor v) {
        v.performActionOnContextStatementBlock(this);
    }

    /* toString */
    public String toString() {
        return ".." +
            super.toString() +
            "\n" +
            "...";
    }

    public int getTypeDeclarationCount() {
        throw new UnsupportedOperationException(getClass() + ": We are not quite a StatementBlock");
    }

    public TypeDeclaration getTypeDeclarationAt(int index) {
        throw new UnsupportedOperationException(getClass() + ": We are not quite a StatementBlock");
    }

    /**
     * overrides the check of the superclass as unmatched elements will disappear in the suffix of
     * this ContextStatementBlock
     */
    public boolean compatibleBlockSize(int pos, int max) {
        return true;
    }

    public MatchConditions match(SourceData source, MatchConditions matchCond) {
        return match(source, matchCond, null);
    }

    /**
     * Matches this context block against the given source. The context bookkeeping is always
     * performed here: locating the active statements under the source's nesting of prefix
     * elements, determining and matching the inner execution context, and recording the positions
     * where the prefix ends and the suffix starts. The active statements themselves are matched by
     * the supplied {@code activeStatements} matcher when one is given (and the located source
     * position is a regular child offset); otherwise by the built-in {@link #matchChildren}. Both
     * yield identical results; a supplied matcher simply matches the active-statement subtrees by
     * direct navigation instead of through their AST {@code match} methods.
     *
     * @param source the source to match against
     * @param matchCond the match conditions found so far
     * @param activeStatements a matcher for the active statements, or {@code null} to use the
     *        built-in {@link #matchChildren}
     * @return the resulting match conditions, or {@code null} if matching fails
     */
    public MatchConditions match(SourceData source, MatchConditions matchCond,
            @Nullable ProgramChildrenMatcher activeStatements) {
        assert getPrefixLength() > 0;
        SourceData newSource = source;

        if (matchCond.getInstantiations().getContextInstantiation() != null) {
            // Currently we do not allow to context statement block
            // occurrences in find or assumes clauses
            return null;
        }

        final ProgramElement src = newSource.getSource();
        final Services services = source.getServices();

        ExecutionContext lastExecutionContext = null;

        final ProgramPrefix prefix;
        int pos = -1;
        PosInProgram relPos = PosInProgram.TOP;

        if (src instanceof ProgramPrefix) {
            prefix = (ProgramPrefix) src;
            final int srcPrefixLength = prefix.getPrefixLength();

            if (getPrefixLength() > srcPrefixLength) {
                return null;
            }

            pos = srcPrefixLength - getPrefixLength();

            ProgramPrefix firstActiveStatement = getPrefixElementAt(prefix, pos);

            relPos = firstActiveStatement.getFirstActiveChildPos();

            // firstActiveStatement contains the ProgramPrefix in front of the first active
            // statement
            // start denotes the child where to start to match
            // in some cases firstActiveStatement already denotes the element to match
            // (empty block, empty try block etc.) this is encoded by setting start to -1
            int start = -1;

            if (relPos != PosInProgram.TOP) {
                if (firstActiveStatement instanceof MethodFrame) {
                    lastExecutionContext = (ExecutionContext) ((MethodFrame) firstActiveStatement)
                            .getExecutionContext();
                }

                start = relPos.get(relPos.depth() - 1);
                if (relPos.depth() > 1) {
                    firstActiveStatement = (ProgramPrefix) PosInProgram.getProgramAt(relPos.up(),
                        firstActiveStatement);
                }
            }
            newSource = new SourceData(firstActiveStatement, start, services);
        } else {
            prefix = null;
        }
        matchCond =
            matchInnerExecutionContext(matchCond, services, lastExecutionContext, prefix, pos, src);

        if (matchCond == null) {
            return null;
        }

        // match the active statements
        final int offset = executionContext == null ? 0 : 1;
        if (activeStatements != null && newSource.getChildPos() >= 0) {
            matchCond = matchActiveStatements(newSource, matchCond, activeStatements, offset);
        } else {
            matchCond = matchChildren(newSource, matchCond, offset);
        }

        if (matchCond == null) {
            return null;
        }

        matchCond =
            makeContextInfoComplete(matchCond, newSource, prefix, pos, relPos, src, services);

        return matchCond;
    }

    /**
     * Matches the active statements via the supplied matcher: this block's children from index
     * {@code offset} against the children of {@code newSource.getElement()} starting at
     * {@code newSource.getChildPos()}. This mirrors
     * {@link #matchChildren(SourceData, MatchConditions, int)} for the case where every active
     * statement consumes exactly one source child. On success the source position is advanced
     * exactly as {@code matchChildren} would, so the subsequent
     * {@link #makeContextInfoComplete} computes the same suffix start.
     */
    private @Nullable MatchConditions matchActiveStatements(SourceData newSource,
            MatchConditions matchCond, ProgramChildrenMatcher activeStatements, int offset) {
        final int startPos = newSource.getChildPos();
        // number of active statements to match (each consumes exactly one source child)
        final int n = getChildCount() - offset;
        final ProgramElement parent = newSource.getElement();
        if (!(parent instanceof NonTerminalProgramElement ntParent)
                || ntParent.getChildCount() < startPos + n) {
            // not enough source children -> matchChildren would also fail (null source child)
            return null;
        }
        final MatchConditions result = (MatchConditions) activeStatements.matchChildrenFrom(
            parent, startPos, matchCond, newSource.getServices());
        if (result == null) {
            return null;
        }
        // advance the source position past the matched children, as matchChildren would
        newSource.setChildPos(startPos + n);
        return result;
    }

    /**
     * completes match of context block by adding the prefix end position and the suffix start
     * position
     */
    private MatchConditions makeContextInfoComplete(MatchConditions matchCond, SourceData newSource,
            ProgramPrefix prefix, int pos, PosInProgram relPos, ProgramElement src,
            Services services) {

        final SVInstantiations instantiations = matchCond.getInstantiations();
        final ExecutionContext lastExecutionContext = instantiations.getExecutionContext();

        final PosInProgram prefixEnd = matchPrefixEnd(prefix, pos, relPos);

        // compute position of the first element not matched
        final int lastMatchedPos = newSource.getChildPos();
        final PosInProgram suffixStart = prefixEnd.up().down(lastMatchedPos);

        /** add context block instantiation */
        matchCond = matchCond.setInstantiations(
            instantiations.replace(prefixEnd, suffixStart, lastExecutionContext, src, services));
        return matchCond;
    }

    /**
     * matches the innermost execution context in prefix, used to resolve references in succeeding
     * matchings
     *
     * @param matchCond
     *        the MatchCond the matchonditions already found
     * @param services
     *        the Services
     * @param lastExecutionContext
     *        the ExecutionContext if already found
     * @param prefix
     *        the oute rmost prefixelement of the original source
     * @param pos
     *        an int as the number of prefix elements to disappear in the context
     * @param src
     *        the original source
     * @return the inner most execution context
     */
    private MatchConditions matchInnerExecutionContext(MatchConditions matchCond,
            final Services services, ExecutionContext lastExecutionContext,
            final ProgramPrefix prefix, int pos, final ProgramElement src) {

        // partial context instantiation

        ExecutionContext innerContext = lastExecutionContext;

        if (innerContext == null) {
            if (prefix != null && prefix.getInnerMostMethodFrame() != null) {
                innerContext =
                    (ExecutionContext) prefix.getInnerMostMethodFrame().getExecutionContext();
            } else {
                innerContext = services.getJavaInfo().getDefaultExecutionContext();
            }
        }

        if (executionContext != null) {
            matchCond =
                executionContext.match(new SourceData(innerContext, -1, services), matchCond);
            if (matchCond == null) {
                return null;
            }
        }

        matchCond = matchCond.setInstantiations(
            matchCond.getInstantiations().add(null, null, innerContext, src, services));

        return matchCond;
    }

    /**
     * computes the PosInProgram of the first element, which is not part of the prefix
     *
     * @param prefix
     *        the ProgramPrefix the outer most prefix element of the source
     * @param pos
     *        the number of elements to disappear in the context
     * @param relPos
     *        the position of the first active statement of element
     *        prefix.getPrefixElementAt(pos);
     * @return the PosInProgram of the first element, which is not part of the prefix
     */
    private PosInProgram matchPrefixEnd(final ProgramPrefix prefix, int pos, PosInProgram relPos) {
        PosInProgram prefixEnd = PosInProgram.TOP;
        if (prefix != null) {
            ProgramPrefix currentPrefix = prefix;
            int i = 0;
            while (i <= pos) {
                // concatenate this prefix element's active-child position in one step instead of
                // iterating + a fresh PosInProgram per position (matchPrefixEnd is the dominant
                // cost of a context match; this avoids an IntIterator and intermediate copies)
                prefixEnd = prefixEnd.append(currentPrefix.getFirstActiveChildPos());
                i++;
                if (i <= pos) {
                    // as fail-fast measure I do not test here using
                    // {@link ProgramPrefix#hasNextPrefixElement()}
                    // It must be guaranteed that there are at least pos + 1
                    // prefix elements (incl. prefix) otherwise there
                    // is a bug already at an earlier point
                    currentPrefix = currentPrefix.getNextPrefixElement();
                }
            }
        } else {
            prefixEnd = relPos;
        }
        return prefixEnd;
    }

    private static ProgramPrefix getPrefixElementAt(ProgramPrefix prefix, int i) {
        ProgramPrefix current = prefix;
        for (int pos = 0; pos < i; pos++) {
            current = current.getNextPrefixElement();
        }
        return current;
    }
}
