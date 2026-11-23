/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import de.uka.ilkd.key.java.transformations.ConstantExpressionEvaluator;
import de.uka.ilkd.key.java.transformations.EvaluationException;

import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.declarations.ResolvedMethodLikeDeclaration;
import com.github.javaparser.resolution.types.ResolvedType;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * Rewrites boxing and unboxing conversions in a JavaParser AST.
 * <p>
 * The rewrite follows JLS 5.1.7 and 5.1.8: boxing becomes
 * {@code Wrapper.valueOf(value)}, unboxing becomes a read of the wrapper's final
 * {@code value} field. Reading the field (instead of calling {@code intValue()}) reuses the
 * existing field-access rules, which split a possibly-null receiver into the happy path and a
 * non-null obligation.
 * <p>
 * Conversions are driven by the expected type of the enclosing context: variable
 * initializers use the declared type, assignments the target type, and return statements the
 * enclosing method's return type. JML specification subtrees are left untouched.
 */
final class AutoboxingRewriter {
    private static final Logger LOGGER = LoggerFactory.getLogger(AutoboxingRewriter.class);
    private static final ConstantExpressionEvaluator CONSTANTS = new ConstantExpressionEvaluator();

    /** Rewrites the given compilation unit in place. */
    void rewrite(CompilationUnit cu) {
        rewriteNode(cu);
    }

    private void rewriteNode(Node node) {
        if (isJml(node)) {
            return;
        }
        if (node instanceof VariableDeclarator declarator) {
            rewriteInitializer(declarator);
        } else if (node instanceof AssignExpr assign
                && assign.getOperator() == AssignExpr.Operator.ASSIGN) {
            rewriteAssignment(assign);
        } else if (node instanceof ReturnStmt returnStmt) {
            rewriteReturn(returnStmt);
        } else if (node instanceof MethodCallExpr call) {
            rewriteCallArguments(call, call::resolve, call.getArguments(), call::setArgument);
        } else if (node instanceof ObjectCreationExpr creation) {
            rewriteCallArguments(creation, creation::resolve, creation.getArguments(),
                creation::setArgument);
        } else if (node instanceof ExplicitConstructorInvocationStmt invocation) {
            rewriteCallArguments(invocation, invocation::resolve, invocation.getArguments(),
                invocation::setArgument);
        }
        for (Node child : new ArrayList<>(node.getChildNodes())) {
            rewriteNode(child);
        }
    }

    private void rewriteInitializer(VariableDeclarator declarator) {
        Expression initializer = declarator.getInitializer().orElse(null);
        if (initializer == null) {
            return;
        }
        declarator.setInitializer(convert(initializer, targetOf(declarator.getType())));
    }

    private void rewriteAssignment(AssignExpr assign) {
        assign.setValue(convert(assign.getValue(), targetOf(assign.getTarget())));
    }

    private void rewriteReturn(ReturnStmt returnStmt) {
        Expression expression = returnStmt.getExpression().orElse(null);
        if (expression == null) {
            return;
        }
        MethodDeclaration method = returnStmt.findAncestor(MethodDeclaration.class).orElse(null);
        if (method == null) {
            return;
        }
        returnStmt.setExpression(convert(expression, targetOf(method.getType())));
    }

    private void rewriteCallArguments(Node node, Resolver resolver, List<Expression> arguments,
            ArgumentSetter setter) {
        ResolvedMethodLikeDeclaration declaration;
        try {
            declaration = resolver.resolve();
        } catch (RuntimeException e) {
            LOGGER.debug("Cannot resolve call {} while rewriting autoboxing", node, e);
            return;
        }
        int parameterCount = declaration.getNumberOfParams();
        boolean variadic = declaration.hasVariadicParameter();
        for (int i = 0; i < arguments.size(); i++) {
            ResolvedType parameterType =
                parameterType(declaration, parameterCount, variadic, i, arguments);
            if (parameterType == null) {
                continue;
            }
            setter.set(i, convert(arguments.get(i), Target.fromResolved(parameterType)));
        }
    }

    private static @Nullable ResolvedType parameterType(ResolvedMethodLikeDeclaration declaration,
            int parameterCount, boolean variadic, int index, List<Expression> arguments) {
        if (parameterCount == 0) {
            return null;
        }
        if (variadic && index >= parameterCount - 1) {
            ResolvedType last = declaration.getParam(parameterCount - 1).getType();
            if (!last.isArray()) {
                return last;
            }
            if (index == parameterCount - 1 && arguments.size() == parameterCount
                    && isArrayOf(arguments.get(index), last)) {
                // The whole array is passed, not one element of the variable arity list.
                return last;
            }
            return last.asArrayType().getComponentType();
        }
        if (index >= parameterCount) {
            return null;
        }
        return declaration.getParam(index).getType();
    }

    private static boolean isArrayOf(Expression expression, ResolvedType arrayType) {
        try {
            ResolvedType actual = expression.calculateResolvedType();
            return actual.isArray() && actual.describe().equals(arrayType.describe());
        } catch (RuntimeException e) {
            return false;
        }
    }

    private static Target targetOf(Type type) {
        if (type.isVarType()) {
            return Target.NONE;
        }
        if (type.isPrimitiveType()) {
            return Target.primitive(type.asPrimitiveType().asString());
        }
        try {
            return Target.fromResolved(type.resolve());
        } catch (RuntimeException e) {
            LOGGER.debug("Cannot resolve type {} while rewriting autoboxing", type, e);
            return Target.NONE;
        }
    }

    private static Target targetOf(Expression expression) {
        try {
            return Target.fromResolved(expression.calculateResolvedType());
        } catch (RuntimeException e) {
            LOGGER.debug("Cannot resolve type of {} while rewriting autoboxing", expression, e);
            return Target.NONE;
        }
    }

    private Expression convert(Expression expression, Target target) {
        if (target.kind() == Kind.NONE || expression.isNullLiteralExpr()) {
            return expression;
        }

        ResolvedType actualType;
        try {
            actualType = expression.calculateResolvedType();
        } catch (RuntimeException e) {
            LOGGER.debug("Cannot resolve type of {} while rewriting autoboxing", expression, e);
            return expression;
        }

        if (actualType.isPrimitive()) {
            String actualPrimitive = actualType.asPrimitive().describe();
            return switch (target.kind()) {
                case PRIMITIVE -> expression;
                case WRAPPER -> box(expression, actualPrimitive, target.wrapper());
                case REFERENCE -> {
                    WrapperType natural = WrapperType.forPrimitive(actualPrimitive);
                    yield natural == null ? expression : box(expression, actualPrimitive, natural);
                }
                default -> expression;
            };
        }

        if (actualType.isReferenceType()) {
            WrapperType wrapper;
            try {
                wrapper = WrapperType.forWrapper(actualType.asReferenceType().getQualifiedName());
            } catch (RuntimeException e) {
                LOGGER.debug("Cannot resolve reference type of {}", expression, e);
                return expression;
            }
            if (wrapper == null) {
                return expression;
            }
            return switch (target.kind()) {
                case PRIMITIVE -> unbox(expression, wrapper, target.primitive());
                case WRAPPER, REFERENCE -> expression;
                default -> expression;
            };
        }

        return expression;
    }

    private static Expression box(Expression expression, String actualPrimitive,
            WrapperType wrapper) {
        Expression inner = expression.clone();
        Expression argument;
        if (actualPrimitive.equals(wrapper.primitiveName())) {
            argument = inner;
        } else if (actualPrimitive.equals("int") && isConstantInRange(expression, wrapper)) {
            argument = cast(wrapper.primitiveName(), inner);
        } else {
            // Not a legal boxing conversion (for example Long l = 1). Leave the program alone so
            // that a normal Java error is reported instead of silently changing the meaning.
            return expression;
        }

        MethodCallExpr call = new MethodCallExpr(
            new NameExpr(wrapper.simpleWrapperName()), "valueOf", NodeList.nodeList(argument));
        copyRange(expression, call);
        return call;
    }

    private static boolean isConstantInRange(Expression expression, WrapperType wrapper) {
        if (wrapper != WrapperType.BYTE && wrapper != WrapperType.SHORT) {
            return false;
        }
        try {
            if (!CONSTANTS.isCompileTimeConstant(expression)) {
                return false;
            }
            Expression value = CONSTANTS.evaluate(expression);
            if (value instanceof IntegerLiteralExpr literal) {
                long number = literal.asNumber().longValue();
                long min = wrapper == WrapperType.BYTE ? Byte.MIN_VALUE : Short.MIN_VALUE;
                long max = wrapper == WrapperType.BYTE ? Byte.MAX_VALUE : Short.MAX_VALUE;
                return min <= number && number <= max;
            }
        } catch (EvaluationException | RuntimeException e) {
            LOGGER.debug("Cannot evaluate constant {}", expression, e);
        }
        return false;
    }

    private static Expression unbox(Expression expression, WrapperType wrapper,
            @Nullable String targetPrimitive) {
        FieldAccessExpr field = new FieldAccessExpr(expression.clone(), wrapper.valueFieldName());
        copyRange(expression, field);
        if (targetPrimitive == null || targetPrimitive.equals(wrapper.primitiveName())) {
            return field;
        }
        if (WrapperType.isWidening(wrapper.primitiveName(), targetPrimitive)) {
            return cast(targetPrimitive, field);
        }
        return expression;
    }

    private static Expression cast(String primitiveName, Expression expression) {
        PrimitiveType type = new PrimitiveType(
            PrimitiveType.Primitive.valueOf(primitiveName.toUpperCase(Locale.ROOT)));
        CastExpr cast = new CastExpr(type, expression);
        copyRange(expression, cast);
        return cast;
    }

    private static void copyRange(Node from, Node to) {
        from.getRange().ifPresent(to::setRange);
    }

    private static boolean isJml(Node node) {
        return node.getClass().getName().startsWith("com.github.javaparser.ast.jml.");
    }

    private enum Kind {
        NONE, PRIMITIVE, WRAPPER, REFERENCE
    }

    @FunctionalInterface
    private interface Resolver {
        ResolvedMethodLikeDeclaration resolve();
    }

    @FunctionalInterface
    private interface ArgumentSetter {
        void set(int index, Expression expression);
    }

    private record Target(Kind kind, @Nullable String primitive, @Nullable WrapperType wrapper) {
        private static final Target NONE = new Target(Kind.NONE, null, null);

        static Target primitive(String name) {
            return new Target(Kind.PRIMITIVE, name, null);
        }

        static Target wrapper(WrapperType type) {
            return new Target(Kind.WRAPPER, null, type);
        }

        static Target reference() {
            return new Target(Kind.REFERENCE, null, null);
        }

        static Target fromResolved(ResolvedType resolved) {
            if (resolved.isPrimitive()) {
                return primitive(resolved.asPrimitive().describe());
            }
            if (resolved.isNull()) {
                return reference();
            }
            if (resolved.isReferenceType()) {
                String name;
                try {
                    name = resolved.asReferenceType().getQualifiedName();
                } catch (RuntimeException e) {
                    return reference();
                }
                WrapperType wrapper = WrapperType.forWrapper(name);
                return wrapper != null ? wrapper(wrapper) : reference();
            }
            return NONE;
        }
    }
}
