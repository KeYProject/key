/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.key.KeyPassiveExpression;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;



/**
 * This class provides static function for constructing AST more efficiently.
 *
 * @author Alexander Weigl
 * @version 1 (15.04.23)
 */
public class AstFactory {
    /**
     * creates the package reference java.lang
     */
    public static ClassOrInterfaceType createJavaLangPackageReference() {
        return new ClassOrInterfaceType(new ClassOrInterfaceType(null, "java"), "lang");
    }

    private static Modifier modifier(Modifier.Keyword mod) {
        return new Modifier(mod);
    }

    public static Modifier mPublic() {
        return modifier(Modifier.Keyword.PUBLIC);
    }

    public static Modifier mStrictFP() {
        return modifier(Modifier.Keyword.STRICTFP);
    }

    public static Modifier mProtected() {
        return modifier(Modifier.Keyword.PROTECTED);
    }

    public static Modifier mPrivate() {
        return modifier(Modifier.Keyword.PRIVATE);
    }

    public static BooleanLiteralExpr mkTrue() {
        return new BooleanLiteralExpr(true);
    }

    public static BooleanLiteralExpr mkFalse() {
        return new BooleanLiteralExpr(false);
    }

    public static IfStmt ifthen(Expression cond, Statement then) {
        return new IfStmt(cond, then, null);
    }

    public static KeyPassiveExpression namePassively(String name) {
        return passive(name(name));
    }

    public static Expression fieldAccessPassively(Expression scope, String variable) {
        return passive(new FieldAccessExpr(scope, variable));
    }

    public static Expression mkThis() {
        return new ThisExpr();
    }

    public static Expression negate(Expression e) {
        return new UnaryExpr(e, UnaryExpr.Operator.LOGICAL_COMPLEMENT);
    }

    public static BlockStmt block(NodeList<Statement> statements) {
        return new BlockStmt(statements);
    }

    public static Statement callPassively(String methodName) {
        return new ExpressionStmt(passive(call(methodName)));
    }

    public static ExpressionStmt callPassively(NameExpr scope, String name) {
        return new ExpressionStmt(passive(new MethodCallExpr(scope, name)));
    }

    public static ThrowStmt throwName(String name) {
        return new ThrowStmt(name(name));
    }


    public static MethodCallExpr call(String s) {
        return new MethodCallExpr(s);
    }


    public static Expression call(TypeExpr typeExpr, String name, NodeList<Expression> arguments) {
        return new MethodCallExpr(typeExpr, name, arguments);
    }

    public static ExpressionStmt calls(String name) {
        return new ExpressionStmt(call(name));
    }


    public static ExpressionStmt assign(Expression lhs, Expression rhs) {
        return mark(new ExpressionStmt(new AssignExpr(lhs, rhs, AssignExpr.Operator.ASSIGN)));
    }

    public static NameExpr name(String name) {
        return new NameExpr(new SimpleName(name));
    }

    public static KeyPassiveExpression passive(Expression e) {
        return new KeyPassiveExpression(e);
    }

    public static ExpressionStmt assignToPassive(String lhs, Expression rhs) {
        return assign(passive(name(lhs)), rhs);
    }

    public static Expression attribute(Expression context, String field) {
        return new FieldAccessExpr(context, field);
    }

    public static <T extends Node> T mark(T node) {
        final var stackTrace = Thread.currentThread().getStackTrace();
        StackTraceElement cur, next = null;
        for (int i = 0; i < stackTrace.length - 1; i++) {
            cur = stackTrace[i];
            next = stackTrace[i + 1];
            if (cur.getClassName().equals(AstFactory.class.getName()) &&
                    !next.getClassName().equals(AstFactory.class.getName()))
                break;
        }
        node.setLineComment(
            String.format("Created by %s:%d", next.getFileName(), next.getLineNumber()));
        return node;
    }
}
