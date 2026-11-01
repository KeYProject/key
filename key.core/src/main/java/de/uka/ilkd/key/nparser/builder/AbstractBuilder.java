/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.nparser.builder;

import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.nparser.JavaKeYParserBaseVisitor;
import de.uka.ilkd.key.util.parsing.BuildingException;
import de.uka.ilkd.key.util.parsing.BuildingIssue;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * This class brings some nice features to the visitors of key's ast.
 *
 * <ul>
 * <li>It makes casting implicit by using {{@link #accept(RuleContext)}}
 * <li>It allows to pass arguments by an explicit stack.
 * <li>It brings handling of errors and warnings.
 * </ul>
 *
 * @param <T>
 *        return type
 * @author Alexander Weigl
 */
@SuppressWarnings("unchecked")
@NullMarked
abstract class AbstractBuilder<T> extends JavaKeYParserBaseVisitor<T> {
    private static final Logger LOGGER = LoggerFactory.getLogger(AbstractBuilder.class);
    private @Nullable List<BuildingIssue> buildingIssues = null;
    private @Nullable Stack<Object> parameters = null;

    /**
     * Helper function for avoiding cast.
     */
    public <U> @Nullable U accept(@Nullable RuleContext ctx) {
        if (ctx == null) {
            return null;
        }
        return (U) ctx.accept(this);
    }

    @Override
    protected T aggregateResult(T aggregate, T nextResult) {
        if (nextResult != null) {
            return nextResult;
        }
        return aggregate;
    }

    @SuppressWarnings("nullness:cast.unsafe") // the stack holds only caller-typed builder values
    protected <U> @Nullable U peek() {
        return (U) (parameters == null || parameters.isEmpty() ? null : parameters.peek());
    }

    /**
     * Accepts the first element of the given non-empty sequence; {@code null} if the sequence is
     * empty. Falls back to {@link #accept(RuleContext)} on the first element.
     */
    protected <U> @Nullable U acceptFirst(Collection<? extends RuleContext> seq) {
        if (seq.isEmpty()) {
            return null;
        }
        return accept(seq.iterator().next());
    }

    protected <U> U pop() {
        if (parameters == null) {
            throw new IllegalStateException("Stack is empty");
        }
        return (U) parameters.pop();
    }

    protected void push(Object... obj) {
        if (parameters == null) {
            parameters = new Stack<>();
        }
        for (Object a : obj) {
            parameters.push(a);
        }
    }

    /**
     * Accepts the given rule context, pushing the arguments onto the param stack and restoring
     * the stack depth afterwards.
     * <p>
     * The param stack is (re)initialized before its size is read; the flow analysis cannot see
     * through the field assignment, hence the dereference of the (nullable) stack field is
     * suppressed with a scoped key.
     */
    @SuppressWarnings("nullness:dereference.of.nullable")
    protected <U> @Nullable U accept(@Nullable RuleContext ctx, Object... args) {
        if (parameters == null) {
            parameters = new Stack<>();
        }
        int stackSize = parameters.size();
        push(args);
        U t = accept(ctx);
        // Stack hygiene
        while (parameters.size() > stackSize) {
            parameters.pop();
        }
        return t;
    }

    /**
     * Accepts the first non-null parser rule context of the given contexts, or {@code null} if
     * all are null.
     */
    protected <U> @Nullable U oneOf(ParserRuleContext... ctxs) {
        for (ParserRuleContext ctx : ctxs) {
            if (ctx != null) {
                return (U) ctx.accept(this);
            }
        }
        return null;
    }

    protected <U> List<U> mapOf(Collection<? extends ParserRuleContext> argument) {
        return argument.stream().map(it -> (U) it.accept(this)).filter(Objects::nonNull)
                .collect(Collectors.toList());
    }

    protected void each(RuleContext... ctx) {
        for (RuleContext c : ctx) {
            accept(c);
        }
    }

    protected void each(Collection<? extends ParserRuleContext> argument) {
        for (RuleContext c : argument) {
            accept(c);
        }
    }
    // endregion

    @SuppressWarnings("nullness:cast.unsafe") // accept() results match the caller-typed roles
    protected <T2> List<T2> mapMapOf(List<? extends RuleContext>... ctxss) {
        return Arrays.stream(ctxss).flatMap(it -> it.stream().map(a -> (T2) accept(a)))
                .collect(Collectors.toList());
    }

    public @NonNull List<BuildingIssue> getBuildingIssues() {
        if (buildingIssues == null) {
            buildingIssues = new LinkedList<>();
        }
        return buildingIssues;
    }

    protected void addWarning(ParserRuleContext ctx, @Nullable Exception e, String message) {
        BuildingIssue be = BuildingIssue.createWarning(message, ctx, e);
        getBuildingIssues().add(be);
    }

    protected void addWarning(ParserRuleContext node, String description) {
        addWarning(node, null, description);
    }

    protected void addWarning(String description) {
        BuildingIssue be = BuildingIssue.createWarning(description, (ParserRuleContext) null, null);
        getBuildingIssues().add(be);
    }
    // endregion

    // region error handling

    /**
     * Throws a semanticError for the given ast node and message. The ast node may be
     * <code>null</code> when no precise source location is available. The generic return type
     * allows the call to be used as a <code>return</code> expression on the (unreachable) paths
     * that exit solely by throwing; the type parameter is never instantiated with a value.
     *
     * @param <T> any desired return type
     * @param ctx the ast node describing the error location, may be null
     */
    protected <T> T semanticError(@Nullable ParserRuleContext ctx, String format, Object... args) {
        throw new BuildingException(ctx == null ? null : ctx.start, null,
            String.format(format, args), null);
    }

    /**
     * Wraps an exception into a {@link BuildingException}. The generic return type allows the call
     * to be used as a <code>return</code> expression on paths that exit solely by throwing; the
     * type parameter is never instantiated with a value.
     *
     * @param <T> any desired return type
     */
    protected <T> T throwEx(Throwable e) {
        throw new BuildingException(e);
    }
    // endregion
}
