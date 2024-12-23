/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations;

import com.github.javaparser.StaticJavaParser;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.key.KeyEscapeExpression;
import com.github.javaparser.ast.key.KeyPassiveExpression;
import com.github.javaparser.ast.key.KeyRangeExpression;
import com.github.javaparser.ast.key.sv.KeyExpressionSV;
import com.github.javaparser.ast.key.sv.KeyMetaConstructExpression;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;

/**
 * An evaluator for constant expression based.
 *
 * @author Alexander Weigl
 * @version 1 (11/2/21)
 */
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

    private Expression toLiteral(Object value) throws EvaluationException {
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
        throw new EvaluationException("Can not express the given value as a literal", null);
    }

    public Expression evaluate(String string) throws EvaluationException {
        return evaluate(StaticJavaParser.parseExpression(string));
    }

    private class ConstantExpressionEvaluatorVisitor extends GenericVisitorAdapter<Object, Void> {
        @Override
        public Object visit(ArrayAccessExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(ArrayCreationExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(ArrayInitializerExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(AssignExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(BinaryExpr n, Void arg) {
            Object left = n.getLeft().accept(this, arg);
            Object right = n.getRight().accept(this, arg);
            switch (n.getOperator()) {
            case OR:
                if (left instanceof Boolean && right instanceof Boolean)
                    return ((Boolean) left) || (Boolean) right;
                throw new RuntimeException();

            case AND:
                if (left instanceof Boolean && right instanceof Boolean)
                    return ((Boolean) left) && (Boolean) right;
                throw new RuntimeException();

            case BINARY_OR:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) | (Integer) right;
                throw new RuntimeException();

            case BINARY_AND:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) & (Integer) right;
                throw new RuntimeException();

            case XOR:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) ^ (Integer) right;
                throw new RuntimeException();
            case EQUALS:
                return left.equals(right);
            case NOT_EQUALS:
                return !left.equals(right);
            case LESS:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) < (Integer) right;
                throw new RuntimeException();
            case GREATER:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) > (Integer) right;
                throw new RuntimeException();
            case LESS_EQUALS:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) <= (Integer) right;
                throw new RuntimeException();
            case GREATER_EQUALS:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) >= (Integer) right;
                throw new RuntimeException();
            case LEFT_SHIFT:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) << (Integer) right;
                throw new RuntimeException();
            case SIGNED_RIGHT_SHIFT:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) >> (Integer) right;
                throw new RuntimeException();
            case UNSIGNED_RIGHT_SHIFT:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) >>> (Integer) right;
                throw new RuntimeException();
            case PLUS:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) + (Integer) right;
                throw new RuntimeException();
            case MINUS:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) - (Integer) right;
                throw new RuntimeException();
            case MULTIPLY:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) * (Integer) right;
                throw new RuntimeException();
            case DIVIDE:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) / (Integer) right;
                throw new RuntimeException();
            case REMAINDER:
                if (left instanceof Integer && right instanceof Integer)
                    return ((Integer) left) % (Integer) right;
                throw new RuntimeException();
            }
            throw new RuntimeException();
        }

        @Override
        public Object visit(BooleanLiteralExpr n, Void arg) {
            return n.getValue();
        }

        @Override
        public Object visit(CastExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(CharLiteralExpr n, Void arg) {
            return n.getValue().charAt(0);
        }

        @Override
        public Object visit(ClassExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(ConditionalExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(DoubleLiteralExpr n, Void arg) {
            return n.asDouble();
        }

        @Override
        public Object visit(EnclosedExpr n, Void arg) {
            return n.getInner().accept(this, arg);
        }

        @Override
        public Object visit(ExplicitConstructorInvocationStmt n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(FieldAccessExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(InstanceOfExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(IntegerLiteralExpr n, Void arg) {
            return n.asNumber();
        }

        @Override
        public Object visit(LambdaExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(LongLiteralExpr n, Void arg) {
            return n.asNumber();
        }

        @Override
        public Object visit(MarkerAnnotationExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(MethodCallExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(MethodReferenceExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(NameExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(NormalAnnotationExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(NullLiteralExpr n, Void arg) {
            return null;
        }

        @Override
        public Object visit(ObjectCreationExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(SingleMemberAnnotationExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(StringLiteralExpr n, Void arg) {
            return n.asString();
        }

        @Override
        public Object visit(SuperExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(ThisExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(TypeExpr n, Void arg) {
            return super.visit(n, arg);
        }

        @Override
        public Object visit(UnaryExpr n, Void arg) {
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
        public Object visit(VariableDeclarationExpr n, Void arg) {
            throw new RuntimeException("unsupported expression");
        }

        @Override
        public Object visit(SwitchExpr n, Void arg) {
            throw new RuntimeException("unsupported expression");
        }

        @Override
        public Object visit(TextBlockLiteralExpr n, Void arg) {
            return n.asString();
        }

        @Override
        public Object visit(RecordPatternExpr n, Void arg) {
            throw new RuntimeException("unsupported expression");
        }

        @Override
        public Object visit(TypePatternExpr n, Void arg) {
            throw new RuntimeException("unsupported expression");
        }

        @Override
        public Object visit(KeyEscapeExpression n, Void arg) {
            throw new RuntimeException("unsupported expression");

        }

        @Override
        public Object visit(KeyRangeExpression n, Void arg) {
            throw new RuntimeException("unsupported expression");

        }

        @Override
        public Object visit(KeyExpressionSV n, Void arg) {
            throw new RuntimeException("unsupported expression");

        }

        @Override
        public Object visit(KeyMetaConstructExpression n, Void arg) {
            throw new RuntimeException("unsupported expression");
        }

        @Override
        public Object visit(KeyPassiveExpression n, Void arg) {
            throw new RuntimeException("unsupported expression");

        }
    }
}
