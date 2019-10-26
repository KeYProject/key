package de.uka.ilkd.key.nparser;

import antlr.RecognitionException;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.JavaReader;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.visitor.DeclarationProgramVariableCollector;
import de.uka.ilkd.key.java.visitor.ProgramVariableCollector;
import de.uka.ilkd.key.ldt.IntegerLDT;
import de.uka.ilkd.key.ldt.SeqLDT;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.parser.*;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.proof.io.RuleSourceFactory;
import de.uka.ilkd.key.rule.RewriteTaclet;
import de.uka.ilkd.key.rule.RuleSet;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.tacletbuilder.*;
import de.uka.ilkd.key.speclang.ClassInvariant;
import de.uka.ilkd.key.speclang.Contract;
import de.uka.ilkd.key.util.Debug;
import de.uka.ilkd.key.util.Pair;
import org.antlr.v4.runtime.ParserRuleContext;
import org.antlr.v4.runtime.RuleContext;
import org.antlr.v4.runtime.Token;
import org.jetbrains.annotations.Nullable;
import org.key_project.util.collection.*;

import java.io.File;
import java.math.BigInteger;
import java.util.*;
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
