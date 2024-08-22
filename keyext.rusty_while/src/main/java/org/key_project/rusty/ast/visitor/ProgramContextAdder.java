package org.key_project.rusty.ast.visitor;

import org.key_project.rusty.ast.RustyProgramElement;
import org.key_project.rusty.ast.expr.BlockExpression;
import org.key_project.rusty.ast.expr.ContextBlockExpression;
import org.key_project.rusty.ast.stmt.Statement;
import org.key_project.rusty.logic.IntIterator;
import org.key_project.rusty.logic.PosInProgram;
import org.key_project.rusty.rule.inst.ContextBlockExpressionInstantiation;
import org.key_project.util.collection.ImmutableList;
import org.key_project.util.collection.ImmutableSLList;

import java.rmi.UnexpectedException;

/**
 * A context given as {@link ContextBlockExpressionInstantiation} is wrapped around a given
 * {@link RustyProgramElement}.
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
    public RustyProgramElement start(RustyProgramElement context,
                                     ContextBlockExpression putIn, ContextBlockExpressionInstantiation ct) {

        return wrap(context, putIn, ct.prefix().iterator(),
                ct.suffix());
    }

    protected RustyProgramElement wrap(RustyProgramElement context, ContextBlockExpression putIn, IntIterator prefixPos, PosInProgram suffix) {
        RustyProgramElement body;
        
        RustyProgramElement next = prefixPos.hasNext() ? (RustyProgramElement) context.getChild(prefixPos.next()) : null;
        
        if (!prefixPos.hasNext()) {
            return createWrapperBody(context, putIn, suffix);
        } else {
            body = wrap(next, putIn, prefixPos, suffix);
            if (context instanceof BlockExpression be) {
                return createBlockExprWrapper(be, body);
            } else {
                throw new RuntimeException(
                        new UnexpectedException("Unexpected block type: " + context.getClass()));
            }
        }
    }

    /**
     * Replaces the first part in the wrapper block. The replacement is optimized as it just
     * returns the replacement block if it is the only child of the block to be
     * constructed and the child is a block too.
     *
     * @param wrapper the StatementBlock where to replace the first statement
     * @param replacement the StatementBlock that replaces the first statement of the block
     * @return the resulting statement block
     */
    private RustyProgramElement createBlockExprWrapper(BlockExpression wrapper, RustyProgramElement replacement) {
        int childCount = wrapper.getChildCount();
        if (childCount <= 1 && replacement instanceof BlockExpression be) return be;
        var body = wrapper.getStatements().tail();
        body = body.prepend((Statement) replacement);
        return new BlockExpression(body, wrapper.getValue());
    }

    /**
     * inserts the content of the statement block <code>putIn</code> and adds succeeding children of
     * the innermost non-terminal element (usually statement block) in the context.
     *
     * @param wrapper the RustyProgramElement with the context that has to be wrapped
     *        around the content of <code>putIn</code>
     * @param putIn the ContextBlockExpression with content that has to be wrapped by the elements hidden in
     *        the context
     * @param suffix the PosInProgram describing the position of the first element before the suffix
     *        of the context
     * @return the BlockExpression which encloses the content of <code>putIn</code> together with the
     *         succeeding context elements of the innermost context block (attention: in a
     *         case like <code>{{{oldStmnt; list of further stmnt;}} moreStmnts; }</code> only the
     *         underscored part is returned <code>{{ __{putIn;....}__ }moreStmnts;}</code> adding
     *         the other braces including the <code>moreStmnts;</code> part has to be done
     *         elsewhere.
     */
    private BlockExpression createWrapperBody(RustyProgramElement wrapper, ContextBlockExpression putIn, PosInProgram suffix) {
        final int putInLength = putIn.getChildCount();

        // ATTENTION: may be -1
        final int lastChild = suffix.last();

        final int childLeft = wrapper.getChildCount() - lastChild;

        int childrenToAdd = putInLength + childLeft;

        if (wrapper instanceof BlockExpression) --childrenToAdd;

        if (childLeft == 0 || lastChild == -1) {
            return putIn;
        }

        ImmutableList<Statement> body = ImmutableSLList.nil();

        for (int i = 0; i < childrenToAdd; i++) {
            if (i < putInLength) {
                body = body.append((Statement) putIn.getChild(i));
            } else {
                body = body.append((Statement) wrapper.getChild(lastChild + (i - putInLength)));
            }
        }

        return new BlockExpression(body, ((BlockExpression) wrapper).getValue());
    }
}
