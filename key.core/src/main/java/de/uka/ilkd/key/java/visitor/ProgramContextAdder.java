/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import java.rmi.UnexpectedException;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.statement.Exec;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopScopeBlock;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.SynchronizedBlock;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.rule.inst.ContextStatementBlockInstantiation;

import org.key_project.logic.IntIterator;
import org.key_project.util.collection.ImmutableArray;

/**
 * A context given as {@link ContextStatementBlockInstantiation} is wrapped around a given
 * {@link ProgramElement}.
 */
public class ProgramContextAdder {

    /**
     * singleton instance of the program context adder
     */
    public final static ProgramContextAdder INSTANCE = new ProgramContextAdder();

    /**
     * an empty private constructor to ensure the singleton property
     */
    private ProgramContextAdder() {
    }

    /**
     * wraps the context around the statements found in the putIn block
     */
    public JavaNonTerminalProgramElement start(JavaNonTerminalProgramElement context,
            StatementBlock putIn, ContextStatementBlockInstantiation ct) {

        return wrap(context, putIn, ct.prefix().iterator(), ct.prefix().depth(), ct.prefix(),
            ct.suffix());
    }

    protected JavaNonTerminalProgramElement wrap(JavaNonTerminalProgramElement context,
            StatementBlock putIn, IntIterator prefixPos, int prefixDepth, PosInProgram prefix,
            PosInProgram suffix) {

        JavaNonTerminalProgramElement body = null;

        ProgramElement next = prefixPos.hasNext() ? context.getChildAt(prefixPos.next()) : null;

        if (!prefixPos.hasNext()) {
            body = createWrapperBody(context, putIn, suffix);
            // special case labeled statement as a label need not be
            // succeeded by a statement block
            if (context instanceof LabeledStatement) {
                body = createLabeledStatementWrapper((LabeledStatement) context, body);
            } else if (context instanceof ActiveCase ac) {
                body = createActiveCaseWrapper(ac, (StatementBlock) body);
            }
            return body;
        } else {
            body = wrap((JavaNonTerminalProgramElement) next, putIn, prefixPos, prefixDepth, prefix,
                suffix);
            if (context instanceof StatementBlock block) {
                return createStatementBlockWrapper(block, body);
            } else if (context instanceof Try t) {
                return createTryStatementWrapper(t, (StatementBlock) body);
            } else if (context instanceof MethodFrame mf) {
                return createMethodFrameWrapper(mf, (StatementBlock) body);
            } else if (context instanceof LabeledStatement ls) {
                return createLabeledStatementWrapper(ls, body);
            } else if (context instanceof LoopScopeBlock lsb) {
                return createLoopScopeBlockWrapper(lsb, (StatementBlock) body);
            } else if (context instanceof SynchronizedBlock sb) {
                return createSynchronizedBlockWrapper(sb,
                    (StatementBlock) body);
            } else if (context instanceof Exec e) {
                return createExecStatementWrapper(e, (StatementBlock) body);
            } else if (context instanceof Switch sw) {
                return createSwitchWrapper(sw, (ActiveCase) body);
            } else if (context instanceof ActiveCase ac) {
                return createActiveCaseWrapper(ac, (Statement) body);
            } else {
                throw new RuntimeException(
                    new UnexpectedException("Unexpected block type: " + context.getClass()));
            }
        }
    }

    /**
     * inserts the content of the statement block <code>putIn</code> and adds succeeding children of
     * the innermost non-terminal element (usually statement block) in the context.
     *
     * @param wrapper the JavaNonTerminalProgramElement with the context that has to be wrapped
     *        around the content of <code>putIn</code>
     * @param putIn the StatementBlock with content that has to be wrapped by the elements hidden in
     *        the context
     * @param suffix the PosInProgram describing the position of the first element before the suffix
     *        of the context
     * @return the StatementBlock which encloses the content of <code>putIn</code> together with the
     *         succeeding context elements of the innermost context statement block (attention: in a
     *         case like <code>{{{oldStmnt; list of further stmnt;}} moreStmnts; }</code> only the
     *         underscored part is returned <code>{{ __{putIn;....}__ }moreStmnts;}</code> adding
     *         the other braces including the <code>moreStmnts;</code> part has to be done
     *         elsewhere.
     */
    private final StatementBlock createWrapperBody(JavaNonTerminalProgramElement wrapper,
            StatementBlock putIn, PosInProgram suffix) {

        final int putInLength = putIn.getChildCount();

        // ATTENTION: may be -1
        final int lastChild = suffix.last();

        final int childLeft = wrapper.getChildCount() - lastChild;

        final int childrenToAdd = putInLength + childLeft;

        if (childLeft == 0 || lastChild == -1) {
            return putIn;
        }

        final Statement[] body = new Statement[childrenToAdd];

        putIn.getBody().arraycopy(0, body, 0, putInLength);

        for (int i = putInLength; i < childrenToAdd; i++) {
            body[i] = (Statement) wrapper.getChildAt(lastChild + (i - putInLength));
        }

        /*
         * Example: In <code>{{{oldStmnt; list of further stmnt;}} moreStmnts; }</code> where
         * <code>oldStmnt;</code> has to be replaced by the content of <code>putIn</code>. Up to
         * here (including the return statement) the underscored part has been created: <code>{{
         * __{putIn;....}__ }moreStmnts;}</code> Attention: we have not yet added the enclosing
         * braces or even the <code>moreStmnts</code>
         */
        return new StatementBlock(new ImmutableArray<>(body));
    }

    /**
     * Replaces the first statement in the wrapper block. The replacement is optimized as it just
     * returns the replacement block if it is the only child of the statement block to be
     * constructed and the child is a statementblock too.
     *
     * @param wrapper the StatementBlock where to replace the first statement
     * @param replacement the StatementBlock that replaces the first statement of the block
     * @return the resulting statement block
     */
    protected StatementBlock createStatementBlockWrapper(StatementBlock wrapper,
            JavaNonTerminalProgramElement replacement) {
        int childrenCount = wrapper.getStatementCount();
        if (childrenCount <= 1 && replacement instanceof StatementBlock) {
            return (StatementBlock) replacement;
        } else {
            Statement[] body = new Statement[childrenCount > 0 ? childrenCount : 1];
            /* reconstruct block */
            body[0] = (Statement) replacement;
            if (childrenCount - 1 > 0) {
                wrapper.getBody().arraycopy(1, body, 1, childrenCount - 1);
            }
            return new StatementBlock(new ImmutableArray<>(body));
        }
    }

    protected Try createTryStatementWrapper(Try old, StatementBlock body) {
        return new Try(body, old.getBranchList());
    }

    protected ActiveCase createActiveCaseWrapper(ActiveCase old, Statement body) {
        var stmts = old.getBody().toArray(new Statement[0]);
        if (body instanceof StatementBlock bodyBlock) {
            if (stmts[0] instanceof StatementBlock sb && !sb.isEmpty()) {
                stmts[0] = bodyBlock;
            } else {
                stmts = bodyBlock.getBody().toArray(new Statement[0]);
            }
        } else {
            stmts[0] = body;
        }
        return new ActiveCase(stmts);
    }

    protected Switch createSwitchWrapper(Switch old, ActiveCase body) {
        var branches = old.getBranchList().toArray(new Branch[0]);
        branches[0] = body;
        return new Switch(old.getExpression(), branches);
    }

    protected Exec createExecStatementWrapper(Exec old, StatementBlock body) {
        return new Exec(body, old.getBranchList());
    }

    protected MethodFrame createMethodFrameWrapper(MethodFrame old, StatementBlock body) {
        return new MethodFrame(old.getProgramVariable(), old.getExecutionContext(), body,
            old.getPositionInfo());
    }

    protected LabeledStatement createLabeledStatementWrapper(LabeledStatement old,
            JavaNonTerminalProgramElement body) {
        return new LabeledStatement(old.getLabel(),
            body instanceof StatementBlock && body.getChildCount() == 1
                    && !(body.getChildAt(0) instanceof LocalVariableDeclaration)
                            ? (Statement) body.getChildAt(0)
                            : (Statement) body,
            old.getPositionInfo());
    }

    protected LoopScopeBlock createLoopScopeBlockWrapper(LoopScopeBlock old, StatementBlock body) {
        return new LoopScopeBlock(old.getIndexPV(), body);
    }

    protected SynchronizedBlock createSynchronizedBlockWrapper(SynchronizedBlock old,
            StatementBlock body) {
        return new SynchronizedBlock(old.getExpression(), body);
    }

}
