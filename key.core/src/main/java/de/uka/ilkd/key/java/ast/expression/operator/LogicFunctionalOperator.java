/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.ast.expression.operator;

import java.util.List;
import java.util.Objects;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.Comment;
import de.uka.ilkd.key.java.ast.PositionInfo;
import de.uka.ilkd.key.java.ast.ProgramElement;
import de.uka.ilkd.key.java.ast.SourceData;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.Operator;
import de.uka.ilkd.key.java.ast.reference.ExecutionContext;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.pp.PrettyPrinter;
import de.uka.ilkd.key.rule.MatchConditions;

import org.key_project.util.ExtList;
import org.key_project.util.collection.ImmutableArray;

import org.jspecify.annotations.Nullable;

import static de.uka.ilkd.key.pp.PrettyPrinter.*;

/**
 *
 * @author Alexander Weigl
 * @version 1 (4/12/26)
 */
public class LogicFunctionalOperator extends Operator {

    public LogicFunctionalOperator(PositionInfo pi, List<Comment> comments, LogicFunction function,
            Expression... args) {
        super(pi, comments, new ImmutableArray<>(args));
        this.function = Objects.requireNonNull(function);
    }

    public LogicFunctionalOperator(LogicFunction function, Expression... args) {
        super(args);
        this.function = Objects.requireNonNull(function);
    }

    public LogicFunctionalOperator(PositionInfo pi, List<Comment> c, LogicFunction fn,
            ImmutableArray<Expression> args) {
        super(pi, c, args);
        this.function = Objects.requireNonNull(fn);
    }

    public LogicFunctionalOperator(LogicFunction function, ExtList changeList) {
        super(changeList);
        this.function = Objects.requireNonNull(function);
    }


    public enum LogicFunction {
        Intersect(2, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\intersect")),
        SetUnion(2, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\set_union")),
        SetMinus(2, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\set_minus")),
        AllObjects(1, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\all_objects")),
        SeqPut(3, 1, PrimitiveType.JAVA_SEQ, AsFunction("\\seq_upd")),
        SeqGet(1, 1, PrimitiveType.JAVA_INT, AsArrayAccess()),
        SeqReverse(1, 1, PrimitiveType.JAVA_SEQ, AsFunction("\\seq_reverse")),
        AllFields(1, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\all_fields")),
        SeqIndexOf(2, 1, PrimitiveType.JAVA_INT, AsFunction("\\indexOf")),
        SeqSingleton(1, 1, PrimitiveType.JAVA_SEQ, AsFunction("\\seq_singleton")),
        SeqSub(3, 1, PrimitiveType.JAVA_SEQ, AsFunction("\\seq_sub")),
        SeqConcat(2, 1, PrimitiveType.JAVA_SEQ, AsFunction("\\seq_concat")),
        Singleton(1, 1, PrimitiveType.JAVA_LOCSET, AsFunction("\\singleton")),
        SeqLength(1, 1, PrimitiveType.JAVA_INT, AsSuffix("length"));

        public final int arity;
        public final int precedence;
        public final PrimitiveType returnType;
        public final PrettyPrinter.PrintOp format;

        LogicFunction(int arity, int precedence, PrimitiveType returnType,
                PrettyPrinter.PrintOp format) {
            this.arity = arity;
            this.precedence = precedence;
            this.returnType = returnType;
            this.format = format;
        }
    }

    private final LogicFunction function;

    public LogicFunction getFunction() {
        return function;
    }

    @Override
    public int getArity() {
        return function.arity;
    }

    @Override
    public int getPrecedence() {
        return function.precedence;
    }

    @Override
    public int getNotation() {
        return PREFIX;
    }

    @Override
    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
        return javaServ.getJavaInfo().getPrimitiveKeYJavaType(function.returnType);
    }

    @Override
    public @Nullable MatchConditions match(SourceData source, MatchConditions matchCond) {
        final ProgramElement src = source.getSource();
        if (src instanceof LogicFunctionalOperator other) {
            if (getFunction().equals(other.getFunction())) {
                return super.match(source, matchCond);
            }
        }
        return null;
    }

    @Override
    public void visit(Visitor v) {
        v.performActionOnLogicFunctionalOperator(this);
    }

    @Override
    public boolean equals(Object o) {
        if (!(o instanceof LogicFunctionalOperator that))
            return false;
        if (!super.equals(o))
            return false;
        return function == that.function && Objects.equals(that.children, children);
    }

    @Override
    protected int computeHashCode() {
        return Objects.hash(function, children);
    }
}
