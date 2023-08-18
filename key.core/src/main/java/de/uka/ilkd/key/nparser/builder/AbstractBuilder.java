/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.util.*;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;

import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import de.uka.ilkd.key.util.parsing.BuildingException;
import de.uka.ilkd.key.util.parsing.BuildingIssue;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;

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
abstract class AbstractBuilder<T> extends KeYParserBaseVisitor<T> {
    @Nullable
    private List<BuildingIssue> buildingIssues = null;
    @Nullable
    private Stack<Object> parameters = null;

    /**
     * Helper function for avoiding cast.
     *
     * @param ctx
     * @param <T>
     * @return
     */
    public <T> @Nullable T accept(@Nullable RuleContext ctx) {
        if (ctx == null) {
            return null;
        }
        try {
            return (T) ctx.accept(this);
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
     * @param <T>
     * @return
     */
    protected <T> T peek() {
        return (T) (parameters.size() == 0 ? null : parameters.peek());
    }

    protected <T> T acceptFirst(Collection<? extends RuleContext> seq) {
        if (seq.isEmpty()) {
            return null;
        }
        return accept(seq.iterator().next());
    }

    protected <T> T pop() {
        if (parameters == null) {
            throw new IllegalStateException("Stack is empty");
        }
        return (T) parameters.pop();
    }

    protected void push(Object... obj) {
        if (parameters == null) {
            parameters = new Stack<>();
        }
        for (Object a : obj) {
            parameters.push(a);
        }
    }

    protected <T> @Nullable T accept(@Nullable RuleContext ctx, Object... args) {
        if (parameters == null) {
            parameters = new Stack<>();
        }
        int stackSize = parameters.size();
        push(args);
        T t = accept(ctx);
        // Stack hygiene
        while (parameters.size() > stackSize) {
            parameters.pop();
        }
        return t;
    }

    protected <T> T oneOf(ParserRuleContext... ctxs) {
        for (ParserRuleContext ctx : ctxs) {
            if (ctx != null) {
                return (T) ctx.accept(this);
            }
        }
        return null;
    }

    protected <T> List<T> mapOf(Collection<? extends ParserRuleContext> argument) {
        return argument.stream().map(it -> (T) it.accept(this)).collect(Collectors.toList());
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

    protected <T2> List<T2> mapMapOf(List<? extends RuleContext>... ctxss) {
        return Arrays.stream(ctxss).flatMap(it -> it.stream().map(a -> (T2) accept(a)))
                .collect(Collectors.toList());
    }

    public @Nonnull List<BuildingIssue> getBuildingIssues() {
        if (buildingIssues == null) {
            buildingIssues = new LinkedList<>();
        }
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
