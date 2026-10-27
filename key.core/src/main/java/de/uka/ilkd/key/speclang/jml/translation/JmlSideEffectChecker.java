/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang.jml.translation;

import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.InitializerDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.expr.ArrayCreationExpr;
import com.github.javaparser.ast.expr.AssignExpr;
import com.github.javaparser.ast.expr.LambdaExpr;
import com.github.javaparser.ast.expr.ObjectCreationExpr;
import com.github.javaparser.ast.expr.UnaryExpr;
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt;
import com.github.javaparser.ast.jml.stmt.JmlExpressionStmt.JmlStmtKind;
import com.github.javaparser.ast.stmt.BlockStmt;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;

/**
 * Structural guard that rejects specification expressions with potential side effects.
 * <p>
 * JMLtk's expression grammar is a superset of Java's, so assignments ({@code =}, {@code +=},
 * ...), increments/decrements ({@code ++}/{@code --} in prefix and postfix form) and object or
 * array creation ({@code new ...}) parse *inside JML specifications*, even though KeY's JML
 * grammar cannot represent them. A spec clause is required to be side-effect free; instead of
 * guessing whether the clause eventually fails to re-serialize (and silently skipping it in the
 * process), this guard rejects such constructs upfront with a diagnostic that carries the
 * offending operator and its source line.
 * <p>
 * The guard is deliberately a <em>structural</em> check, not a text scan: it walks the parsed
 * JMLtk AST and forbids the concrete node kinds listed below, exactly once, wherever they occur.
 * Method calls are deliberately <em>not</em> forbidden here: calling a pure/helper method in a
 * specification is legal. Purity of called methods is a separate, semantic check.
 * <p>
 * Allowed contexts: the guard only ever descends into specification subtrees (contract and
 * class-level clause expressions, {@code assert}/{@code assume} conditions). Explicitly exempt
 * are {@code set} statements ({@code //@ set x = 5;}) and ghost declarators, where assignment is
 * the point rather than a side effect. Callers pass spec-bearing nodes only (a {@code JmlContract},
 * a class level {@code JmlClassExprDeclaration}/... or a single {@code Expression}); as a safety
 * net the visitor does not descend into Java method/constructor/initializer/lambda bodies or
 * statement blocks at all.
 */
public final class JmlSideEffectChecker extends VoidVisitorAdapter<Void> {

    private JmlSideEffectChecker() {
        // no instances
    }

    /**
     * Runs the side-effect guard on the given spec-bearing node. Throws a
     * {@link JmlSideEffectException} if the subtree contains a forbidden construct.
     *
     * @param node the specification node to check (a JMLtk contract, class level declaration or
     *        expression), or {@code null}.
     */
    public static void check(Node node) {
        if (node != null) {
            node.accept(new JmlSideEffectChecker(), null);
        }
    }

    @Override
    public void visit(AssignExpr n, Void arg) {
        fail(n, "Assignment operator '" + n.getOperator().asString()
            + "' is not allowed in a JML specification expression");
    }

    @Override
    public void visit(UnaryExpr n, Void arg) {
        switch (n.getOperator()) {
            case PREFIX_INCREMENT, PREFIX_DECREMENT, POSTFIX_INCREMENT, POSTFIX_DECREMENT -> fail(n,
                "Increment/decrement operator '" + n.getOperator().asString()
                    + "' is not allowed in a JML specification expression");
            default -> super.visit(n, arg);
        }
    }

    @Override
    public void visit(ObjectCreationExpr n, Void arg) {
        fail(n, "Object creation (new " + n.getType()
            + ") is not allowed in a JML specification expression");
    }

    @Override
    public void visit(ArrayCreationExpr n, Void arg) {
        fail(n, "Array creation (new " + n.getElementType()
            + "[...]) is not allowed in a JML specification expression");
    }

    /**
     * A {@code set} statement ({@code //@ set x = 5;}) assigns by definition; do not descend into
     * it. For other JML expression statements only the caller-provided condition expression is
     * checked, never this node.
     */
    @Override
    public void visit(JmlExpressionStmt n, Void arg) {
        if (n.getKind() != JmlStmtKind.SET) {
            super.visit(n, arg);
        }
    }

    // Safety net: never descend into Java code that may legally contain assignments, even if a
    // caller accidentally passes a node whose subtree contains program statements. Specifications
    // have no method bodies.

    @Override
    public void visit(MethodDeclaration n, Void arg) {
        // no descent
    }

    @Override
    public void visit(ConstructorDeclaration n, Void arg) {
        // no descent
    }

    @Override
    public void visit(InitializerDeclaration n, Void arg) {
        // no descent
    }

    @Override
    public void visit(LambdaExpr n, Void arg) {
        // no descent
    }

    @Override
    public void visit(BlockStmt n, Void arg) {
        // no descent
    }

    private static void fail(Node n, String message) {
        String line = n.getRange().map(r -> " at line " + r.begin.line).orElse("");
        throw new JmlSideEffectException(message + line);
    }
}
