/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.TypeDeclaration;
import com.github.javaparser.ast.stmt.CatchClause;
import com.github.javaparser.ast.stmt.TryStmt;
import com.github.javaparser.ast.type.UnionType;

/// Desugaring of Multi-Catch statements to multiple single catch statements.
/// ## Transformation Rules (per JLS 14.20)
/// ### Multi-Catch:
/// ```java
/// try {
/// body
/// } catch (ExceptionType1 | ExceptionType2 | ExceptionType3 e) {
/// handler
/// }
/// ```
///
/// becomes:
/// ```java
/// try {
/// body
/// } catch (final ExceptionType1 e) {
/// handler
/// } catch (final ExceptionType2 e) {
/// handler
/// } catch (final ExceptionType3 e) {
/// handler
/// }
/// ```
///
/// Important notes:
///
/// - The exception variable `e` in a multi-catch is implicitly final.
/// - Each resulting catch clause gets its own copy of the handler body.
/// - The order of catch clauses follows the order of exception types in the union.
/// - Catch clause ordering must respect subtype relationships (more specific exceptions first).
///
/// @author Alexander Weigl
/// @version 1 (12.07.26)
/// @see [JLS 14.20](https://docs.oracle.com/javase/specs/jls/se21/html/jls-14.html#jls-14.20)
public class MultiCatchReducer implements JavaTransformer {
    @Override
    public void apply(TypeDeclaration<?> td) {
        td.walk(TryStmt.class, this::rewrite);
    }

    /**
     * Rewrites a try statement with multi-catch clauses to use only single catch clauses.
     * Each multi-catch clause is replaced by multiple single-type catch clauses.
     */
    private void rewrite(TryStmt tryStmt) {
        var catchClauses = tryStmt.getCatchClauses();
        var originalClauses = catchClauses.stream().toList();
        var insertAt = 0;
        for (int i = 0; i < originalClauses.size(); i++) {
            CatchClause catchClause = originalClauses.get(i);
            var paramType = catchClause.getParameter().getType();
            if (paramType instanceof UnionType unionType) {
                catchClauses.remove(catchClause); // delete original clause

                // Create individual catch clauses for each exception type in the union
                for (var elementType : unionType.getElements()) {
                    CatchClause newCatchClause = new CatchClause();
                    // Create a new parameter with the single exception type
                    var originalParam = catchClause.getParameter();
                    var newParam = new com.github.javaparser.ast.body.Parameter(
                        elementType.clone(),
                        originalParam.getName().clone());

                    // Copy modifiers (the parameter is implicitly final in multi-catch)
                    newParam.addModifier(Modifier.DefaultKeyword.FINAL);
                    newCatchClause.setParameter(newParam);

                    // Clone the body for each catch clause
                    newCatchClause.setBody(catchClause.getBody().clone());

                    // Insert after the current position (will be before due to reverse iteration)
                    catchClauses.add(insertAt++, newCatchClause);
                }
            } else {
                insertAt++;
            }
        }
    }
}
