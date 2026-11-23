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

import com.github.javaparser.ast.ArrayCreationLevel;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.ArrayAccessExpr;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.ArrayInitializerExpr;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.BinaryExpr;
import com.github.javaparser.ast.expr.CastExpr;
import com.github.javaparser.ast.expr.ConditionalExpr;
import com.github.javaparser.ast.expr.EnclosedExpr;
import com.github.javaparser.ast.expr.Expression;
import com.github.javaparser.ast.expr.FieldAccessExpr;
import com.github.javaparser.ast.expr.IntegerLiteralExpr;
import com.github.javaparser.ast.expr.MethodCallExpr;
import com.github.javaparser.ast.expr.NameExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.SwitchExpr;
import com.github.javaparser.ast.expr.ThisExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.expr.VariableDeclarationExpr;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.stmt.DoStmt;
import com.github.javaparser.ast.stmt.ExplicitConstructorInvocationStmt;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.ForEachStmt;
import com.github.javaparser.ast.stmt.ForStmt;
import com.github.javaparser.ast.stmt.IfStmt;
import com.github.javaparser.ast.stmt.ReturnStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.stmt.SwitchStmt;
import com.github.javaparser.ast.stmt.WhileStmt;
import com.github.javaparser.ast.type.PrimitiveType;
import com.github.javaparser.ast.type.Type;
import com.github.javaparser.resolution.declarations.ResolvedMethodLikeDeclaration;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
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

    private int freshId;

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
        } else if (node instanceof AssignExpr assign) {
            if (assign.getOperator() == AssignExpr.Operator.ASSIGN) {
                rewriteAssignment(assign);
            } else {
                rewriteCompoundAssignment(assign);
            }
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
        } else if (node instanceof BinaryExpr binary) {
            rewriteBinary(binary);
        } else if (node instanceof UnaryExpr unary) {
            rewriteUnary(unary);
        } else if (node instanceof ArrayAccessExpr access) {
            rewriteArrayIndex(access);
        } else if (node instanceof ArrayInitializerExpr initializer) {
            rewriteTopLevelArrayInitializer(initializer);
        } else if (node instanceof ForEachStmt forEach) {
            rewriteForEach(forEach);
        } else if (node instanceof CastExpr cast) {
            rewriteCast(cast);
        } else if (node instanceof IfStmt ifStmt) {
            ifStmt.setCondition(unboxBoolean(ifStmt.getCondition()));
        } else if (node instanceof WhileStmt whileStmt) {
            whileStmt.setCondition(unboxBoolean(whileStmt.getCondition()));
        } else if (node instanceof DoStmt doStmt) {
            doStmt.setCondition(unboxBoolean(doStmt.getCondition()));
        } else if (node instanceof ForStmt forStmt) {
            forStmt.getCompare().ifPresent(compare -> forStmt.setCompare(unboxBoolean(compare)));
        } else if (node instanceof ConditionalExpr conditional) {
            rewriteConditional(conditional);
        } else if (node instanceof SwitchStmt switchStmt) {
            switchStmt.setSelector(unboxWrapper(switchStmt.getSelector()));
        } else if (node instanceof SwitchExpr switchExpr) {
            switchExpr.setSelector(unboxWrapper(switchExpr.getSelector()));
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
        if (initializer instanceof ArrayInitializerExpr arrayInitializer
                && declarator.getType().isArrayType()) {
            List<ArrayCreationLevel> levels = new ArrayList<>();
            Type elementType = baseElementType(declarator.getType(), levels);
            if (elementType != null && !levels.isEmpty()) {
                ArrayCreationExpr creation = new ArrayCreationExpr(elementType,
                    NodeList.nodeList(levels), arrayInitializer.clone());
                copyRange(initializer, creation);
                declarator.setInitializer(creation);
                return;
            }
        }
        declarator.setInitializer(convert(initializer, targetOf(declarator.getType())));
    }

    private static @Nullable Type baseElementType(Type arrayType,
            List<ArrayCreationLevel> levels) {
        Type current = arrayType;
        while (current.isArrayType()) {
            levels.add(new ArrayCreationLevel());
            current = current.asArrayType().getComponentType();
        }
        return current;
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

    private void rewriteCast(CastExpr cast) {
        Target target = targetOf(cast.getType());
        if (target.kind() == Kind.NONE) {
            return;
        }
        Expression operand = cast.getExpression();
        ResolvedType actual = typeOf(operand);
        if (actual == null) {
            return;
        }
        if (actual.isPrimitive()) {
            String primitive = actual.asPrimitive().describe();
            if (target.kind() == Kind.WRAPPER) {
                Expression boxed = box(operand, primitive, target.wrapper());
                if (boxed != operand) {
                    cast.replace(boxed);
                }
            } else if (target.kind() == Kind.REFERENCE) {
                WrapperType natural = WrapperType.forPrimitive(primitive);
                if (natural != null) {
                    Expression boxed = box(operand, primitive, natural);
                    if (boxed != operand) {
                        cast.setExpression(boxed);
                    }
                }
            }
        } else if (actual.isReferenceType()) {
            WrapperType wrapper = wrapperOf(actual);
            if (wrapper != null && target.kind() == Kind.PRIMITIVE) {
                cast.replace(unboxForCast(operand, wrapper, target.primitive()));
            }
        }
    }

    private void rewriteConditional(ConditionalExpr conditional) {
        conditional.setCondition(unboxBoolean(conditional.getCondition()));
        Expression thenExpr = conditional.getThenExpr();
        Expression elseExpr = conditional.getElseExpr();
        ResolvedType thenType = typeOf(thenExpr);
        ResolvedType elseType = typeOf(elseExpr);
        String thenPrimitive = numericPrimitive(thenType);
        String elsePrimitive = numericPrimitive(elseType);
        if (thenPrimitive != null && elsePrimitive != null) {
            String promoted = promote(thenPrimitive, elsePrimitive);
            conditional.setThenExpr(widen(thenExpr, thenType, thenPrimitive, promoted));
            conditional.setElseExpr(widen(elseExpr, elseType, elsePrimitive, promoted));
            return;
        }
        if (isBooleanLike(thenExpr) && isBooleanLike(elseExpr)) {
            conditional.setThenExpr(unboxBoolean(thenExpr));
            conditional.setElseExpr(unboxBoolean(elseExpr));
        }
    }

    private static boolean isBooleanLike(Expression expression) {
        ResolvedType type = typeOf(expression);
        if (type == null) {
            return false;
        }
        if (type.isPrimitive()) {
            return "boolean".equals(type.asPrimitive().describe());
        }
        return wrapperOf(type) == WrapperType.BOOLEAN;
    }

    private static Expression unboxForCast(Expression expression, WrapperType wrapper,
            String targetPrimitive) {
        Expression field = new FieldAccessExpr(expression.clone(), wrapper.valueFieldName());
        return targetPrimitive.equals(wrapper.primitiveName())
                ? field
                : cast(targetPrimitive, field);
    }

    private void rewriteCompoundAssignment(AssignExpr assign) {
        if (!isSimpleTarget(assign.getTarget())) {
            return;
        }
        ResolvedType targetType = typeOf(assign.getTarget());
        String lhsPrimitive = numericPrimitive(targetType);
        if (lhsPrimitive == null) {
            return;
        }
        BinaryExpr.Operator binaryOperator = binaryOperator(assign.getOperator());
        if (binaryOperator == null) {
            return;
        }
        ResolvedType rhsType = typeOf(assign.getValue());
        String rhsPrimitive = numericPrimitive(rhsType);
        if (rhsPrimitive == null) {
            return;
        }
        boolean boxedLhs = targetType.isReferenceType();
        if (!boxedLhs && (rhsType == null || !rhsType.isReferenceType())) {
            // Primitive lhs and primitive rhs: the existing widening rules suffice.
            return;
        }

        String lhsPromoted;
        String rhsPromoted;
        if (isShift(binaryOperator)) {
            lhsPromoted = lhsPrimitive.equals("long") ? "long" : "int";
            rhsPromoted = rhsPrimitive.equals("long") ? "long" : "int";
        } else {
            String promoted = promote(lhsPrimitive, rhsPrimitive);
            lhsPromoted = promoted;
            rhsPromoted = promoted;
        }

        Expression lhsRead = boxedLhs
                ? new FieldAccessExpr(assign.getTarget().clone(),
                    wrapperOf(targetType).valueFieldName())
                : assign.getTarget().clone();
        Expression promotedLhs = widenPrimitive(lhsRead, lhsPrimitive, lhsPromoted);
        Expression rhs = widen(assign.getValue().clone(), rhsType, rhsPrimitive, rhsPromoted);
        Expression operation = new BinaryExpr(promotedLhs, rhs, binaryOperator);
        Expression narrowed = cast(lhsPrimitive, operation);
        Expression value =
            boxedLhs ? boxPrimitive(wrapperOf(targetType), narrowed) : narrowed;
        assign.setOperator(AssignExpr.Operator.ASSIGN);
        assign.setValue(value);
    }

    private void rewriteIncrement(UnaryExpr unary) {
        UnaryExpr.Operator operator = unary.getOperator();
        boolean increment = operator == UnaryExpr.Operator.PREFIX_INCREMENT
                || operator == UnaryExpr.Operator.POSTFIX_INCREMENT;
        boolean prefix = operator.isPrefix();
        Expression operand = unary.getExpression();
        if (!isSimpleTarget(operand)) {
            return;
        }
        WrapperType wrapper = wrapperOf(typeOf(operand));
        if (wrapper == null || !isNumericName(wrapper.primitiveName())) {
            return;
        }
        String primitive = wrapper.primitiveName();
        if (!prefix && !isIntegral(primitive)) {
            // The old-value arithmetic below is only exact for the integral types.
            return;
        }

        Expression read = new FieldAccessExpr(operand.clone(), wrapper.valueFieldName());
        Expression changed = new BinaryExpr(read, new IntegerLiteralExpr("1"),
            increment ? BinaryExpr.Operator.PLUS : BinaryExpr.Operator.MINUS);
        AssignExpr assignment = new AssignExpr(operand,
            boxPrimitive(wrapper, cast(primitive, changed)), AssignExpr.Operator.ASSIGN);
        Expression value = new FieldAccessExpr(new EnclosedExpr(assignment),
            wrapper.valueFieldName());

        if (prefix) {
            unary.replace(value);
        } else {
            Expression old = new BinaryExpr(value, new IntegerLiteralExpr("1"),
                increment ? BinaryExpr.Operator.MINUS : BinaryExpr.Operator.PLUS);
            unary.replace(cast(primitive, old));
        }
    }

    private static boolean isIncrement(UnaryExpr.Operator operator) {
        return operator == UnaryExpr.Operator.PREFIX_INCREMENT
                || operator == UnaryExpr.Operator.PREFIX_DECREMENT
                || operator == UnaryExpr.Operator.POSTFIX_INCREMENT
                || operator == UnaryExpr.Operator.POSTFIX_DECREMENT;
    }

    private static BinaryExpr.@Nullable Operator binaryOperator(AssignExpr.Operator operator) {
        return switch (operator) {
            case PLUS -> BinaryExpr.Operator.PLUS;
            case MINUS -> BinaryExpr.Operator.MINUS;
            case MULTIPLY -> BinaryExpr.Operator.MULTIPLY;
            case DIVIDE -> BinaryExpr.Operator.DIVIDE;
            case REMAINDER -> BinaryExpr.Operator.REMAINDER;
            case BINARY_AND -> BinaryExpr.Operator.BINARY_AND;
            case BINARY_OR -> BinaryExpr.Operator.BINARY_OR;
            case XOR -> BinaryExpr.Operator.XOR;
            case LEFT_SHIFT -> BinaryExpr.Operator.LEFT_SHIFT;
            case SIGNED_RIGHT_SHIFT -> BinaryExpr.Operator.SIGNED_RIGHT_SHIFT;
            case UNSIGNED_RIGHT_SHIFT -> BinaryExpr.Operator.UNSIGNED_RIGHT_SHIFT;
            default -> null;
        };
    }

    private static boolean isSimpleTarget(Expression target) {
        if (target instanceof NameExpr || target instanceof ThisExpr) {
            return true;
        }
        if (target instanceof FieldAccessExpr field) {
            return isSimpleTarget(field.getScope());
        }
        return false;
    }

    private static @Nullable WrapperType wrapperOf(@Nullable ResolvedType type) {
        if (type == null || !type.isReferenceType()) {
            return null;
        }
        try {
            return WrapperType.forWrapper(type.asReferenceType().getQualifiedName());
        } catch (RuntimeException e) {
            return null;
        }
    }

    private static boolean isIntegral(String primitive) {
        return switch (primitive) {
            case "byte", "short", "char", "int", "long" -> true;
            default -> false;
        };
    }

    private static Expression widenPrimitive(Expression expression, String from, String to) {
        if (from.equals(to)) {
            return expression;
        }
        if (WrapperType.isWidening(from, to)) {
            return cast(to, expression);
        }
        return expression;
    }

    private static Expression boxPrimitive(WrapperType wrapper, Expression primitive) {
        return new MethodCallExpr(new NameExpr(wrapper.simpleWrapperName()), "valueOf",
            NodeList.nodeList(primitive));
    }

    private void rewriteBinary(BinaryExpr binary) {
        BinaryExpr.Operator operator = binary.getOperator();
        if (operator == BinaryExpr.Operator.EQUALS
                || operator == BinaryExpr.Operator.NOT_EQUALS) {
            if (isPrimitiveNumeric(binary.getLeft()) || isPrimitiveNumeric(binary.getRight())) {
                promoteBinary(binary);
            }
            return;
        }
        if (operator == BinaryExpr.Operator.AND || operator == BinaryExpr.Operator.OR) {
            binary.setLeft(unboxBoolean(binary.getLeft()));
            binary.setRight(unboxBoolean(binary.getRight()));
            return;
        }
        if (isShift(operator)) {
            rewriteShift(binary);
            return;
        }
        if (!isNumericBinary(operator) || isStringConcat(binary)) {
            return;
        }
        promoteBinary(binary);
    }

    private void promoteBinary(BinaryExpr binary) {
        ResolvedType leftType = typeOf(binary.getLeft());
        ResolvedType rightType = typeOf(binary.getRight());
        String leftPrimitive = numericPrimitive(leftType);
        String rightPrimitive = numericPrimitive(rightType);
        if (leftPrimitive == null || rightPrimitive == null) {
            return;
        }
        String promoted = promote(leftPrimitive, rightPrimitive);
        binary.setLeft(widen(binary.getLeft(), leftType, leftPrimitive, promoted));
        binary.setRight(widen(binary.getRight(), rightType, rightPrimitive, promoted));
    }

    private void rewriteShift(BinaryExpr binary) {
        ResolvedType leftType = typeOf(binary.getLeft());
        ResolvedType rightType = typeOf(binary.getRight());
        String leftPrimitive = numericPrimitive(leftType);
        String rightPrimitive = numericPrimitive(rightType);
        if (leftPrimitive == null || rightPrimitive == null) {
            return;
        }
        String leftPromoted = leftPrimitive.equals("long") ? "long" : "int";
        String rightPromoted = rightPrimitive.equals("long") ? "long" : "int";
        binary.setLeft(widen(binary.getLeft(), leftType, leftPrimitive, leftPromoted));
        binary.setRight(widen(binary.getRight(), rightType, rightPrimitive, rightPromoted));
    }

    private void rewriteUnary(UnaryExpr unary) {
        if (isIncrement(unary.getOperator())) {
            rewriteIncrement(unary);
            return;
        }
        switch (unary.getOperator()) {
            case PLUS, MINUS, BITWISE_COMPLEMENT -> {
                ResolvedType type = typeOf(unary.getExpression());
                String primitive = numericPrimitive(type);
                if (primitive == null) {
                    return;
                }
                String promoted = switch (primitive) {
                    case "byte", "short", "char" -> "int";
                    default -> primitive;
                };
                unary.setExpression(widen(unary.getExpression(), type, primitive, promoted));
            }
            case LOGICAL_COMPLEMENT -> unary.setExpression(unboxBoolean(unary.getExpression()));
            default -> {
            }
        }
    }

    private void rewriteArrayIndex(ArrayAccessExpr access) {
        ResolvedType type = typeOf(access.getIndex());
        String primitive = numericPrimitive(type);
        if (primitive == null) {
            return;
        }
        access.setIndex(widen(access.getIndex(), type, primitive, "int"));
    }

    private void rewriteTopLevelArrayInitializer(ArrayInitializerExpr initializer) {
        Node parent = initializer.getParentNode().orElse(null);
        ResolvedType componentType = null;
        if (parent instanceof ArrayCreationExpr creation) {
            ResolvedType arrayType = typeOf(creation);
            if (arrayType != null && arrayType.isArray()) {
                componentType = arrayType.asArrayType().getComponentType();
            }
        } else if (parent instanceof VariableDeclarator declarator) {
            ResolvedType arrayType = resolveType(declarator.getType());
            if (arrayType != null && arrayType.isArray()) {
                componentType = arrayType.asArrayType().getComponentType();
            }
        }
        rewriteArrayInitializer(initializer, componentType);
    }

    private void rewriteArrayInitializer(ArrayInitializerExpr initializer,
            @Nullable ResolvedType componentType) {
        if (componentType == null) {
            return;
        }
        Target target = Target.fromResolved(componentType);
        ResolvedType nestedComponent =
            componentType.isArray() ? componentType.asArrayType().getComponentType() : null;
        for (Expression value : initializer.getValues()) {
            if (value instanceof ArrayInitializerExpr nested) {
                rewriteArrayInitializer(nested, nestedComponent);
                continue;
            }
            ResolvedType actualType = typeOf(value);
            if (actualType == null) {
                continue;
            }
            Expression converted = convertKnown(value, actualType, target);
            if (converted != value) {
                value.replace(converted);
            }
        }
    }

    private void rewriteForEach(ForEachStmt forEach) {
        ResolvedType iterableType = typeOf(forEach.getIterable());
        if (iterableType == null || !iterableType.isArray()) {
            return;
        }
        if (!isSimpleTarget(forEach.getIterable())) {
            // Keep side-effecting iterables unchanged rather than evaluating them repeatedly.
            return;
        }
        ResolvedType componentType = iterableType.asArrayType().getComponentType();
        VariableDeclarationExpr variable = forEach.getVariable();
        if (variable.getVariables().size() != 1) {
            return;
        }
        VariableDeclarator declarator = variable.getVariable(0);
        Target target = targetOf(declarator.getType());
        if (!needsConversion(componentType, target)) {
            // No boxing/unboxing: keep the enhanced-for so the prover's elimination (and its
            // loop contracts and \index/\values support) remains intact.
            return;
        }
        Expression iterable = forEach.getIterable();

        int id = ++freshId;
        String indexName = "$keYIndex" + id;
        ArrayAccessExpr element = new ArrayAccessExpr(iterable.clone(), new NameExpr(indexName));
        declarator.setInitializer(convertKnown(element, componentType, target));

        Statement body = forEach.getBody();
        BlockStmt bodyBlock = body instanceof BlockStmt block ? block
                : new BlockStmt(NodeList.nodeList(body));
        bodyBlock.getStatements().add(0, new ExpressionStmt(variable));

        Expression compare = new BinaryExpr(new NameExpr(indexName),
            new FieldAccessExpr(iterable.clone(), "length"), BinaryExpr.Operator.LESS);
        Expression update =
            new UnaryExpr(new NameExpr(indexName), UnaryExpr.Operator.POSTFIX_INCREMENT);
        VariableDeclarationExpr indexDeclaration = new VariableDeclarationExpr(
            new VariableDeclarator(new PrimitiveType(PrimitiveType.Primitive.INT), indexName,
                new IntegerLiteralExpr("0")));
        ForStmt loop = new ForStmt(NodeList.nodeList(indexDeclaration), compare,
            NodeList.nodeList(update), bodyBlock);

        copyRange(forEach, loop);
        forEach.replace(loop);
        rewriteNode(loop);
    }

    private static @Nullable ResolvedType resolveType(Type type) {
        try {
            return type.resolve();
        } catch (RuntimeException e) {
            return null;
        }
    }

    /**
     * Tells whether the element type needs a boxing or unboxing conversion for the loop variable.
     * Primitive widening and reference assignments are left to the existing rules.
     */
    private static boolean needsConversion(@Nullable ResolvedType componentType, Target target) {
        if (componentType == null || target.kind() == Kind.NONE) {
            return false;
        }
        if (componentType.isPrimitive()) {
            String primitive = componentType.asPrimitive().describe();
            if (target.kind() == Kind.WRAPPER) {
                return true;
            }
            if (target.kind() == Kind.REFERENCE) {
                return WrapperType.forPrimitive(primitive) != null;
            }
            return false;
        }
        if (componentType.isReferenceType()) {
            WrapperType wrapper = wrapperOf(componentType);
            return wrapper != null && target.kind() == Kind.PRIMITIVE;
        }
        return false;
    }

    private static Expression unboxBoolean(Expression expression) {
        ResolvedType type = typeOf(expression);
        if (type != null && type.isReferenceType()) {
            try {
                WrapperType wrapper = WrapperType
                        .forWrapper(type.asReferenceType().getQualifiedName());
                if (wrapper == WrapperType.BOOLEAN) {
                    return unbox(expression, wrapper, wrapper.primitiveName());
                }
            } catch (RuntimeException e) {
                LOGGER.debug("Cannot resolve boolean operand {}", expression, e);
            }
        }
        return expression;
    }

    private static Expression unboxWrapper(Expression expression) {
        ResolvedType type = typeOf(expression);
        if (type != null && type.isReferenceType()) {
            try {
                WrapperType wrapper = WrapperType
                        .forWrapper(type.asReferenceType().getQualifiedName());
                if (wrapper != null) {
                    return unbox(expression, wrapper, null);
                }
            } catch (RuntimeException e) {
                LOGGER.debug("Cannot resolve switch selector {}", expression, e);
            }
        }
        return expression;
    }

    private static @Nullable ResolvedType typeOf(Expression expression) {
        // JavaParser reports the operand type for ++/-- and !, but the value of these
        // expressions has the unboxed primitive type. Correcting this here keeps the
        // conversion pass from wrapping an increment expression in an unboxing itself.
        if (expression instanceof UnaryExpr unary) {
            if (isIncrement(unary.getOperator())) {
                ResolvedType operand = typeOf(unary.getExpression());
                WrapperType wrapper = wrapperOf(operand);
                return wrapper != null
                        ? ResolvedPrimitiveType.byName(wrapper.primitiveName())
                        : operand;
            }
            if (unary.getOperator() == UnaryExpr.Operator.LOGICAL_COMPLEMENT) {
                return ResolvedPrimitiveType.BOOLEAN;
            }
        }
        if (expression instanceof ConditionalExpr conditional) {
            String thenPrimitive = numericPrimitive(typeOf(conditional.getThenExpr()));
            String elsePrimitive = numericPrimitive(typeOf(conditional.getElseExpr()));
            if (thenPrimitive != null && elsePrimitive != null) {
                return ResolvedPrimitiveType.byName(promote(thenPrimitive, elsePrimitive));
            }
            if (isBooleanLike(conditional.getThenExpr())
                    && isBooleanLike(conditional.getElseExpr())) {
                return ResolvedPrimitiveType.BOOLEAN;
            }
        }
        if (expression instanceof BinaryExpr binary) {
            BinaryExpr.Operator operator = binary.getOperator();
            if (operator == BinaryExpr.Operator.EQUALS
                    || operator == BinaryExpr.Operator.NOT_EQUALS
                    || operator == BinaryExpr.Operator.LESS
                    || operator == BinaryExpr.Operator.GREATER
                    || operator == BinaryExpr.Operator.LESS_EQUALS
                    || operator == BinaryExpr.Operator.GREATER_EQUALS
                    || operator == BinaryExpr.Operator.AND
                    || operator == BinaryExpr.Operator.OR) {
                return ResolvedPrimitiveType.BOOLEAN;
            }
            if (isShift(operator)) {
                String left = numericPrimitive(typeOf(binary.getLeft()));
                if (left != null) {
                    return ResolvedPrimitiveType.byName(left.equals("long") ? "long" : "int");
                }
            } else if (isNumericBinary(operator) && !isStringConcat(binary)) {
                String left = numericPrimitive(typeOf(binary.getLeft()));
                String right = numericPrimitive(typeOf(binary.getRight()));
                if (left != null && right != null) {
                    return ResolvedPrimitiveType.byName(promote(left, right));
                }
            }
        }
        try {
            return expression.calculateResolvedType();
        } catch (RuntimeException e) {
            return null;
        }
    }

    private static @Nullable String numericPrimitive(@Nullable ResolvedType type) {
        if (type == null) {
            return null;
        }
        if (type.isPrimitive()) {
            String name = type.asPrimitive().describe();
            return isNumericName(name) ? name : null;
        }
        if (type.isReferenceType()) {
            try {
                WrapperType wrapper = WrapperType
                        .forWrapper(type.asReferenceType().getQualifiedName());
                if (wrapper != null && isNumericName(wrapper.primitiveName())) {
                    return wrapper.primitiveName();
                }
            } catch (RuntimeException e) {
                return null;
            }
        }
        return null;
    }

    private static boolean isPrimitiveNumeric(Expression expression) {
        ResolvedType type = typeOf(expression);
        return type != null && type.isPrimitive() && isNumericName(type.asPrimitive().describe());
    }

    private static boolean isNumericName(String name) {
        return switch (name) {
            case "byte", "short", "char", "int", "long", "float", "double" -> true;
            default -> false;
        };
    }

    private static String promote(String left, String right) {
        if (left.equals("double") || right.equals("double")) {
            return "double";
        }
        if (left.equals("float") || right.equals("float")) {
            return "float";
        }
        if (left.equals("long") || right.equals("long")) {
            return "long";
        }
        return "int";
    }

    private static Expression widen(Expression expression, @Nullable ResolvedType actualType,
            String actualPrimitive, String target) {
        if (actualType == null) {
            return expression;
        }
        if (actualType.isReferenceType()) {
            WrapperType wrapper = WrapperType.forPrimitive(actualPrimitive);
            return wrapper == null ? expression : unbox(expression, wrapper, target);
        }
        if (actualPrimitive.equals(target)) {
            return expression;
        }
        if (WrapperType.isWidening(actualPrimitive, target)) {
            return cast(target, expression.clone());
        }
        return expression;
    }

    private static boolean isShift(BinaryExpr.Operator operator) {
        return operator == BinaryExpr.Operator.LEFT_SHIFT
                || operator == BinaryExpr.Operator.SIGNED_RIGHT_SHIFT
                || operator == BinaryExpr.Operator.UNSIGNED_RIGHT_SHIFT;
    }

    private static boolean isNumericBinary(BinaryExpr.Operator operator) {
        return switch (operator) {
            case PLUS, MINUS, MULTIPLY, DIVIDE, REMAINDER, LESS, GREATER, LESS_EQUALS,
                    GREATER_EQUALS, BINARY_AND, BINARY_OR, XOR ->
                true;
            default -> false;
        };
    }

    private static boolean isStringConcat(BinaryExpr binary) {
        if (binary.getOperator() != BinaryExpr.Operator.PLUS) {
            return false;
        }
        return isString(typeOf(binary.getLeft())) || isString(typeOf(binary.getRight()));
    }

    private static boolean isString(@Nullable ResolvedType type) {
        if (type == null || !type.isReferenceType()) {
            return false;
        }
        try {
            return "java.lang.String".equals(type.asReferenceType().getQualifiedName());
        } catch (RuntimeException e) {
            return false;
        }
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
        ResolvedType actualType = typeOf(expression);
        return actualType == null ? expression : convertKnown(expression, actualType, target);
    }

    private static Expression convertKnown(Expression expression, ResolvedType actualType,
            Target target) {
        if (target.kind() == Kind.NONE || expression.isNullLiteralExpr()) {
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
