/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import de.uka.ilkd.key.util.parsing.BuildingException;
import de.uka.ilkd.key.util.parsing.BuildingIssue;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.jspecify.annotations.Nullable;

import java.util.*;

/**
 * This class brings some nice features to the visitors of key's ast.
 *
 * <ul>
 * <li>It makes casting implicit by using {{@link #accept(RuleContext)}}
 * <li>It allows to pass arguments by an explicit stack.
 * <li>It brings handling of errors and warnings.
 * </ul>
 *
 * @param <T> return type
 * @author Alexander Weigl
 */
@SuppressWarnings("unchecked")
abstract class AbstractBuilder<T extends @Nullable Object> extends KeYParserBaseVisitor<T> {
    private final List<BuildingIssue> buildingIssues = new ArrayList<>(1);
    private Stack<Object> parameters = new Stack<>();

    /**
     * Helper function for avoiding cast.
     *
     * @param ctx
     * @param <R>
     * @return
     */
    public <R extends T> R accept(@Nullable RuleContext ctx) {
        if (ctx == null) {
            return null;
        }
        try {
            return (R) ctx.accept(this);
        } catch (Exception e) {
            if (!(e instanceof BuildingException) && ctx instanceof ParserRuleContext) {
                throw new BuildingException((ParserRuleContext) ctx, e);
            }
            // otherwise we rethrow
            throw e;
        }
    }

    @Override
    protected T aggregateResult(T aggregate, T nextResult) {
        if (nextResult != null) {
            return nextResult;
        }
        return aggregate;
    }

    /**
     * @param <R>
     * @return
     */
    protected <R extends @Nullable Object> R peek() {
        return (R) (parameters.isEmpty() ? null : parameters.peek());
    }

    protected <R extends T> R acceptFirst(Collection<? extends RuleContext> seq) {
        if (seq.isEmpty()) {
            return null;
        }
        return accept(seq.iterator().next());
    }

    protected <R> R pop() {
        return (R) parameters.pop();
    }

    protected void push(Object... obj) {
        for (Object a : obj) {
            parameters.push(a);
        }
    }

    protected <R extends T> R accept(@Nullable RuleContext ctx, Object... args) {
        int stackSize = parameters.size();
        push(args);
        R t = accept(ctx);
        // Stack hygiene
        while (parameters.size() > stackSize) {
            parameters.pop();
        }
        return t;
    }

    protected <R extends T> R oneOf(@Nullable ParserRuleContext... ctxs) {
        for (ParserRuleContext ctx : ctxs) {
            if (ctx != null) {
                return (R) ctx.accept(this);
            }
        }
        return null;
    }

    protected <R extends T> List<R> mapOf(Collection<? extends ParserRuleContext> argument) {
        return argument.stream()
                .map(it -> (R) it.accept(this))
                .toList();
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

    protected <T2 extends T> List<T2> mapMapOf(List<? extends RuleContext>... ctxss) {
        return Arrays.stream(ctxss).flatMap(it -> it.stream().map(a -> (T2) accept(a)))
                .toList();
    }

    public List<BuildingIssue> getBuildingIssues() {
        return buildingIssues;
    }

    protected BuildingIssue addWarning(ParserRuleContext node, String description) {
        BuildingIssue be = BuildingIssue.createWarning(description, node, null);
        getBuildingIssues().add(be);
        return be;
    }

    protected BuildingIssue addWarning(String description) {
        BuildingIssue be = BuildingIssue.createWarning(description, (ParserRuleContext) null, null);
        getBuildingIssues().add(be);
        return be;
    }
    // endregion

    // region error handling

    /**
     * Throws a semanticError for the given ast node and message.
     *
     * @param ctx
     * @param format
     * @param args
     */
    protected void semanticError(ParserRuleContext ctx, String format, Object... args) {
        throw new BuildingException(ctx, String.format(format, args));
    }

    /**
     * Wraps an exception into a {@link BuildingException}
     *
     * @param e
     */
    protected void throwEx(Throwable e) {
        throw new BuildingException(e);
    }
    // endregion
}
