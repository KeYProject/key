/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations;

import java.util.LinkedList;
import java.util.Objects;
import java.util.Queue;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.key.KeyEscapeExpression;
import com.github.javaparser.ast.key.KeyPassiveExpression;
import com.github.javaparser.ast.key.sv.KeyExpressionSV;
import com.github.javaparser.ast.key.sv.KeyMetaConstructExpression;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * An evaluator for constant expression in Java.
 *
 * @author Alexander Weigl
 * @version 1 (11/2/21)
 */
@NullMarked
public class ConstantExpressionEvaluator {
    public boolean isCompileTimeConstant(Expression expr) throws EvaluationException {
        var ccev = new ConstantExpressionEvaluatorVisitor();
        try {
            expr.accept(ccev, null);
            return true;
        } catch (RuntimeException e) {
            return false;
        }
    }

    public Expression evaluate(Expression expression) throws EvaluationException {
        var ccev = new ConstantExpressionEvaluatorVisitor();
        try {
            Object value = expression.accept(ccev, null);
            return toLiteral(value);
        } catch (RuntimeException e) {
            throw new EvaluationException("", e);
        }
    }

    private Expression toLiteral(@Nullable Object value) throws EvaluationException {
        if (value instanceof String) {
            return new StringLiteralExpr(value.toString());
        }
        if (value instanceof Integer) {
            return new IntegerLiteralExpr(value.toString());
        }
        if (value instanceof Float) {
            return new DoubleLiteralExpr(value + "f");
        }
        if (value instanceof Double) {
            return new DoubleLiteralExpr(value + "D");
        }
        if (value instanceof Short) {
            return new IntegerLiteralExpr(value + "D");
        }
        if (value instanceof Long) {
            return new IntegerLiteralExpr(value + "L");
        }
        if (value instanceof Byte) {
            return new IntegerLiteralExpr(value.toString());
        }
        if (value instanceof Character) {
            return new CharLiteralExpr(value.toString());
        }
        throw new EvaluationException("Can not express the given value as a literal",
            new RuntimeException());
    }

    public Expression evaluate(String string) throws EvaluationException {
        return evaluate(StaticJavaParser.parseExpression(string));
    }

    private static class ConstantExpressionEvaluatorVisitor
            extends GenericVisitorAdapter<@Nullable Object, Void> {

        private final Queue<FieldDeclaration> path = new LinkedList<>();

        @Override
        public @Nullable Object visit(ArrayAccessExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(ArrayCreationExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(ArrayInitializerExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(AssignExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(BinaryExpr n, Void arg) {
            Object left = n.getLeft().accept(this, arg);
            Object right = n.getRight().accept(this, arg);
            return switch (n.getOperator()) {
                case IMPLICATION, ANTIVALENCE, EQUIVALENCE, RIMPLICATION, SUB_LOCKE, SUB_LOCK,
                        RANGE, SUBTYPE ->
                    throw new RuntimeException();
                case OR -> {
                    if (left instanceof Boolean && right instanceof Boolean)
                        yield ((Boolean) left) || (Boolean) right;
                    throw new RuntimeException();
                }
                case AND -> {
                    if (left instanceof Boolean && right instanceof Boolean)
                        yield ((Boolean) left) && (Boolean) right;
                    throw new RuntimeException();
                }
                case BINARY_OR -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) | (Integer) right;
                    throw new RuntimeException();
                }
                case BINARY_AND -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) & (Integer) right;
                    throw new RuntimeException();
                }
                case XOR -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) ^ (Integer) right;
                    throw new RuntimeException();
                }
                case EQUALS -> Objects.requireNonNull(left).equals(right);
                case NOT_EQUALS -> !Objects.requireNonNull(left).equals(right);
                case LESS -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) < (Integer) right;
                    throw new RuntimeException();
                }
                case GREATER -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) > (Integer) right;
                    throw new RuntimeException();
                }
                case LESS_EQUALS -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) <= (Integer) right;
                    throw new RuntimeException();
                }
                case GREATER_EQUALS -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) >= (Integer) right;
                    throw new RuntimeException();
                }
                case LEFT_SHIFT -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) << (Integer) right;
                    throw new RuntimeException();
                }
                case SIGNED_RIGHT_SHIFT -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) >> (Integer) right;
                    throw new RuntimeException();
                }
                case UNSIGNED_RIGHT_SHIFT -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) >>> (Integer) right;
                    throw new RuntimeException();
                }
                case PLUS -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) + (Integer) right;
                    throw new RuntimeException();
                }
                case MINUS -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) - (Integer) right;
                    throw new RuntimeException();
                }
                case MULTIPLY -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) * (Integer) right;
                    throw new RuntimeException();
                }
                case DIVIDE -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) / (Integer) right;
                    throw new RuntimeException();
                }
                case REMAINDER -> {
                    if (left instanceof Integer && right instanceof Integer)
                        yield ((Integer) left) % (Integer) right;
                    throw new RuntimeException();
                }
            };
        }

        @Override
        public @Nullable Object visit(BooleanLiteralExpr n, Void arg) {
            return n.getValue();
        }

        @Override
        public @Nullable Object visit(CastExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(CharLiteralExpr n, Void arg) {
            return n.getValue().charAt(0);
        }

        @Override
        public @Nullable Object visit(ClassExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(ConditionalExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(DoubleLiteralExpr n, Void arg) {
            return n.asDouble();
        }

        @Override
        public @Nullable Object visit(EnclosedExpr n, Void arg) {
            return n.getInner().accept(this, arg);
        }

        @Override
        public @Nullable Object visit(ExplicitConstructorInvocationStmt n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(FieldAccessExpr n, Void arg) {
            final FieldDeclaration fd = Objects.requireNonNull(
                (FieldDeclaration) n.resolve().asField().toAst().orElse(null));
            if (fd.isFinal() && fd.isStatic() && !path.contains(fd)) {
                path.add(fd);
                var result = super.visit(fd, arg);
                path.remove(fd);
                return result;
            } else {
                return null;
            }
        }

        @Override
        public @Nullable Object visit(InstanceOfExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(IntegerLiteralExpr n, Void arg) {
            return n.asNumber();
        }

        @Override
        public @Nullable Object visit(LambdaExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(LongLiteralExpr n, Void arg) {
            return n.asNumber();
        }

        @Override
        public @Nullable Object visit(MarkerAnnotationExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(MethodCallExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(MethodReferenceExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(NameExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(NormalAnnotationExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(NullLiteralExpr n, Void arg) {
            return null;
        }

        @Override
        public @Nullable Object visit(ObjectCreationExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(SingleMemberAnnotationExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(StringLiteralExpr n, Void arg) {
            return n.asString();
        }

        @Override
        public @Nullable Object visit(SuperExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(ThisExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(TypeExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public @Nullable Object visit(UnaryExpr n, Void arg) {
            Object value = n.getExpression().accept(this, arg);
            switch (n.getOperator()) {
                case PLUS:
                    return value;
                case MINUS:
                    if (value instanceof Integer)
                        return -(Integer) value;
                    if (value instanceof Long)
                        return -(Long) value;
                    if (value instanceof Byte)
                        return -(Byte) value;
                    if (value instanceof Short)
                        return -(Short) value;
                    if (value instanceof Double)
                        return -(Double) value;
                    if (value instanceof Float)
                        return -(Float) value;
                    throw new RuntimeException();
                case PREFIX_INCREMENT:
                case POSTFIX_INCREMENT:
                    if (value instanceof Integer)
                        return 1 + (Integer) value;
                    if (value instanceof Long)
                        return 1 + (Long) value;
                    if (value instanceof Byte)
                        return 1 + (Byte) value;
                    if (value instanceof Short)
                        return 1 + (Short) value;
                    if (value instanceof Double)
                        return 1 + (Double) value;
                    if (value instanceof Float)
                        return 1 + (Float) value;
                    throw new RuntimeException();
                case PREFIX_DECREMENT:
                case POSTFIX_DECREMENT:
                    if (value instanceof Integer)
                        return ((Integer) value) - 1;
                    if (value instanceof Long)
                        return ((Long) value) - 1;
                    if (value instanceof Byte)
                        return ((Byte) value) - 1;
                    if (value instanceof Short)
                        return ((Short) value) - 1;
                    if (value instanceof Double)
                        return ((Double) value) - 1;
                    if (value instanceof Float)
                        return ((Float) value) - 1;
                    throw new RuntimeException();
                case LOGICAL_COMPLEMENT:
                    if (value instanceof Boolean)
                        return !(Boolean) value;
                    throw new RuntimeException();
                case BITWISE_COMPLEMENT:
                    if (value instanceof Integer)
                        return ~((Integer) value);
                    if (value instanceof Long)
                        return ~((Long) value);
                    if (value instanceof Byte)
                        return ~((Byte) value);
                    if (value instanceof Short)
                        return ~((Short) value);
            }
            throw new RuntimeException("unsupported expression");
        }

        @Override
        public @Nullable Object visit(VariableDeclarationExpr n, Void arg) {
            throw new RuntimeException("unsupported expression");
        }

        @Override
        public @Nullable Object visit(SwitchExpr n, Void arg) {
            throw new RuntimeException("unsupported expression");
        }

        @Override
        public @Nullable Object visit(TextBlockLiteralExpr n, Void arg) {
            return n.asString();
        }

        @Override
        public @Nullable Object visit(RecordPatternExpr n, Void arg) {
            throw new RuntimeException("unsupported expression");
        }

        @Override
        public @Nullable Object visit(TypePatternExpr n, Void arg) {
            throw new RuntimeException("unsupported expression");
        }

        @Override
        public @Nullable Object visit(KeyEscapeExpression n, Void arg) {
            throw new RuntimeException("unsupported expression");

        }

        @Override
        public @Nullable Object visit(KeyExpressionSV n, Void arg) {
            throw new RuntimeException("unsupported expression");

        }

        @Override
        public @Nullable Object visit(KeyMetaConstructExpression n, Void arg) {
            throw new RuntimeException("unsupported expression");
        }

        @Override
        public @Nullable Object visit(KeyPassiveExpression n, Void arg) {
            throw new RuntimeException("unsupported expression");

        }
    }
}
