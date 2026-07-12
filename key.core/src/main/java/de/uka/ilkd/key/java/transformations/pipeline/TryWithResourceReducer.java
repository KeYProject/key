package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.Parameter;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.body.VariableDeclarator;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.ClassOrInterfaceType;
import com.github.javaparser.ast.visitor.ModifierVisitor;
import com.github.javaparser.ast.visitor.Visitable;

import java.util.List;
import java.util.concurrent.atomic.AtomicInteger;

/// Rewrites every try-with-resources statement into the equivalent nested
/// try/finally form that javac itself generates, i.e. for
/// ```java
/// try (Resource r = open()) {
///     body;
/// }
/// ```
/// this produces:
/// ```java
/// try {
///     Resource r = open();
///     Throwable primaryExc$1 = null;
///     try {
///         body;
///     } catch (Throwable t$1) {
///         primaryExc$1 = t$1;
///         throw t$1;
///     } finally {
///         if (r != null) {
///             if (primaryExc$1 != null) {
///                 try { r.close(); } catch (Throwable suppressedExc$1) {
///                     primaryExc$1.addSuppressed(suppressedExc$1);
///                 }
///             } else { r.close(); }
///         }
///     }
/// }
/// ```
/// Multiple resources are handled by nesting (last-declared resource closes first),
/// and any catch/finally clauses that were attached to the original try are kept
/// on an outer try that wraps the whole resource-management block, exactly as
/// javac does it.
/// @author weigl, Claude Sonnet
public class TryWithResourceReducer implements JavaTransformer {
    private final AtomicInteger counter = new AtomicInteger();

    @Override
    public void apply(TypeDeclaration<?> td) {
        td.accept(new TryWithResourcesDesugarer(), null);
    }

    public class TryWithResourcesDesugarer extends ModifierVisitor<Void> {
        @Override
        public Visitable visit(TryStmt n, Void arg) {
            // Desugar nested try statements first (in body/catches/finally) before
            // handling this one, so everything ends up fully expanded.
            super.visit(n, arg);

            if (n.getResources().isEmpty()) {
                return n;
            }

            List<Expression> resources = n.getResources();
            BlockStmt innerBody = desugarResources(resources, 0, n.getTryBlock().clone());

            // If the original try had no catch/finally of its own, the resource
            // management block *is* the whole replacement.
            if (n.getCatchClauses().isEmpty() && n.getFinallyBlock().isEmpty()) {
                return innerBody;
            }

            // Otherwise wrap the resource-management block in a try that keeps the
            // user's original catch clauses / finally block.
            TryStmt outer = new TryStmt();
            outer.setTryBlock(innerBody);
            outer.setCatchClauses(n.getCatchClauses());
            n.getFinallyBlock().ifPresent(outer::setFinallyBlock);
            return outer;
        }

        /**
         * Recursively builds the resource-closing nest starting at resources.get(index),
         * with `body` as the innermost block (the original try-block statements).
         */
        private BlockStmt desugarResources(List<Expression> resources, int index, BlockStmt body) {
            BlockStmt result = new BlockStmt();

            Expression resourceExpr = resources.get(index);
            String resourceName;

            if (resourceExpr instanceof VariableDeclarationExpr) {
                // try (Resource r = new Resource()) { ... }
                VariableDeclarationExpr vde = (VariableDeclarationExpr) resourceExpr;
                VariableDeclarator vd = vde.getVariable(0);
                resourceName = vd.getNameAsString();
                result.addStatement(new ExpressionStmt(vde.clone()));
            } else {
                // Java 9+ form: try (existingEffectivelyFinalVar) { ... }
                // No declaration needed -- the variable already exists in scope.
                resourceName = resourceExpr.toString();
            }

            int id = counter.incrementAndGet();
            String primaryExcName = "primaryExc$" + id;
            String throwableName = "t$" + id;
            String suppressedExcName = "suppressedExc$" + id;

            result.addStatement(declareVar("Throwable", primaryExcName, new NullLiteralExpr()));

            BlockStmt innerTryBlock = (index + 1 < resources.size())
                    ? desugarResources(resources, index + 1, body)
                    : body;

            // catch (Throwable t$n) { primaryExc$n = t$n; throw t$n; }
            CatchClause catchClause = new CatchClause();
            catchClause.setParameter(new Parameter(new ClassOrInterfaceType(null, "Throwable"), throwableName));
            BlockStmt catchBody = new BlockStmt();
            catchBody.addStatement(new ExpressionStmt(
                    new AssignExpr(new NameExpr(primaryExcName), new NameExpr(throwableName), AssignExpr.Operator.ASSIGN)));
            catchBody.addStatement(new ThrowStmt(new NameExpr(throwableName)));
            catchClause.setBody(catchBody);

            // finally { if (r != null) { if (primaryExc$n != null) { try { r.close(); } catch (Throwable s) { primaryExc$n.addSuppressed(s); } } else { r.close(); } } }
            BlockStmt finallyBlock = new BlockStmt();

            IfStmt excCheck = new IfStmt();
            excCheck.setCondition(notNull(new NameExpr(primaryExcName)));

            TryStmt closeWithSuppression = new TryStmt();
            BlockStmt closeTryBlock = new BlockStmt();
            closeTryBlock.addStatement(new ExpressionStmt(closeCall(resourceName)));
            closeWithSuppression.setTryBlock(closeTryBlock);

            CatchClause suppressCatch = new CatchClause();
            suppressCatch.setParameter(new Parameter(new ClassOrInterfaceType(null, "Throwable"), suppressedExcName));
            BlockStmt suppressBody = new BlockStmt();
            suppressBody.addStatement(new ExpressionStmt(new MethodCallExpr(
                    new NameExpr(primaryExcName), "addSuppressed", NodeList.nodeList(new NameExpr(suppressedExcName)))));
            suppressCatch.setBody(suppressBody);
            closeWithSuppression.setCatchClauses(NodeList.nodeList(suppressCatch));

            excCheck.setThenStmt(closeWithSuppression);

            BlockStmt plainClose = new BlockStmt();
            plainClose.addStatement(new ExpressionStmt(closeCall(resourceName)));
            excCheck.setElseStmt(plainClose);

            IfStmt nullCheck = new IfStmt();
            nullCheck.setCondition(notNull(new NameExpr(resourceName)));
            BlockStmt nullCheckThen = new BlockStmt();
            nullCheckThen.addStatement(excCheck);
            nullCheck.setThenStmt(nullCheckThen);

            finallyBlock.addStatement(nullCheck);

            TryStmt resourceTry = new TryStmt();
            resourceTry.setTryBlock(innerTryBlock);
            resourceTry.setCatchClauses(NodeList.nodeList(catchClause));
            resourceTry.setFinallyBlock(finallyBlock);

            result.addStatement(resourceTry);
            return result;
        }

        private static BinaryExpr notNull(Expression e) {
            return new BinaryExpr(e, new NullLiteralExpr(), BinaryExpr.Operator.NOT_EQUALS);
        }

        private static MethodCallExpr closeCall(String resourceName) {
            return new MethodCallExpr(new NameExpr(resourceName), "close");
        }

        private static Statement declareVar(String typeName, String varName, Expression initializer) {
            VariableDeclarator vd = new VariableDeclarator(new ClassOrInterfaceType(null, typeName), varName, initializer);
            return new ExpressionStmt(new VariableDeclarationExpr(vd));
        }
    }
}