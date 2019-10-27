package de.uka.ilkd.key.nparser;

import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.jetbrains.annotations.Nullable;

import java.util.Collection;
import java.util.List;
import java.util.Stack;
import java.util.stream.Collectors;

abstract class AbstractBuilder<T> extends KeYParserBaseVisitor<T> {
    //region stack handling
    private Stack<Object> parameters = new Stack<>();

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
        return (T) ctx.accept(this);
    }

    void each(RuleContext... ctx) {
        for (RuleContext c : ctx) accept(c);
    }

    protected <T> T peek() {
        return (T) (parameters.size() == 0 ? null : parameters.peek());
    }


    protected <T> T pop() {
        return (T) parameters.pop();
    }

    protected void push(Object... obj) {
        for (Object a : obj) parameters.push(a);
    }

    protected <T> @Nullable T accept(@Nullable RuleContext ctx, Object... args) {
        int stackSize = parameters.size();
        push(args);
        T t = accept(ctx);
        //Stack hygiene
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

    protected <T> List<T> allOf(Collection<? extends ParserRuleContext> argument) {
        return argument.stream().map(it -> (T) it.accept(this)).collect(Collectors.toList());
    }

    public <T> List<T> mapOf(List<? extends ParserRuleContext> seq) {
        return seq.stream().map(it -> (T) it.accept(this))
                .collect(Collectors.toList());
    }

}
