/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.nparser.builder;

import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.nparser.KeYParserBaseVisitor;
import de.uka.ilkd.key.util.parsing.BuildingException;
import de.uka.ilkd.key.util.parsing.BuildingExceptions;
import de.uka.ilkd.key.util.parsing.BuildingIssue;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;

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
    private static final Logger LOGGER = LoggerFactory.getLogger(AbstractBuilder.class);
    @Nullable
    private List<BuildingIssue> buildingIssues = null;
    @Nullable
    private Stack<Object> parameters = null;

    /**
     * Helper function for avoiding cast.
     */
    public <U> @Nullable U accept(@Nullable RuleContext ctx) {
        if (ctx == null) {
            return null;
        }
        try {
            return (U) ctx.accept(this);
        } catch (BuildingExceptions | BuildingException e) {
            throw e;
        } catch (Exception e) {
            LOGGER.error("", e);
            if (ctx instanceof ParserRuleContext) {
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

    protected <U> U peek() {
        return (U) (parameters == null || parameters.isEmpty() ? null : parameters.peek());
    }

    protected <U> U acceptFirst(Collection<? extends RuleContext> seq) {
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

    protected <U> U oneOf(ParserRuleContext... ctxs) {
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

    protected void addWarning(ParserRuleContext ctx, Exception e, String message) {
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
     * Throws a semanticError for the given ast node and message.
     */
    protected void semanticError(ParserRuleContext ctx, String format, Object... args) {
        throw new BuildingException(ctx, String.format(format, args));
    }

    /**
     * Wraps an exception into a {@link BuildingException}
     */
    protected void throwEx(Throwable e) {
        throw new BuildingException(e);
    }
    // endregion
}
