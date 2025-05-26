/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.ast.visitor;

import org.key_project.logic.op.sv.SchemaVariable;
import org.key_project.rusty.ast.PathInExpression;
import org.key_project.rusty.ast.expr.*;
import org.key_project.rusty.ast.pat.*;
import org.key_project.rusty.ast.stmt.EmptyStatement;
import org.key_project.rusty.ast.stmt.ExpressionStatement;
import org.key_project.rusty.ast.stmt.LetStatement;
import org.key_project.rusty.ast.ty.*;
import org.key_project.rusty.logic.op.ProgramFunction;
import org.key_project.rusty.logic.op.ProgramVariable;
import org.key_project.rusty.rule.metaconstruct.ProgramTransformer;
import org.key_project.rusty.speclang.LoopSpecification;

/**
 * This class is implemented by visitors/walkers. Each AST node implements a visit(Visitor) method
 * that calls the doActionAt<NodeType> method. Similar to the pretty print mechanism.
 */
public interface Visitor {
    void performActionOnAssignmentExpression(AssignmentExpression x);

    void performActionOnBlockExpression(BlockExpression x);

    void performActionOnBooleanLiteralExpression(BooleanLiteralExpression x);

    void performActionOnContextBlockExpression(ContextBlockExpression x);

    void performActionOnIntegerLiteralExpression(IntegerLiteralExpression x);

    void performActionOnSchemaVariable(SchemaVariable x);

    void performActionOnProgramVariable(ProgramVariable x);

    void performActionOnEmptyStatement(EmptyStatement x);

    void performActionOnMethodCall(MethodCallExpression x);

    void performActionOnFieldExpression(FieldExpression x);

    void performActionOnTupleIndexingExpression(TupleIndexingExpression x);

    void performActionOnCallExpression(CallExpression x);

    void performActionOnIndexExpression(IndexExpression x);

    void performActionOnErrorPropagationExpression(ErrorPropagationExpression x);

    void performActionOnBorrowExpression(BorrowExpression x);

    void performActionOnDereferenceExpression(DereferenceExpression x);

    void performActionOnTypeCastExpression(TypeCastExpression x);

    void performActionOnRangeExpression(RangeExpression x);

    void performActionOnCompoundAssignmentExpression(CompoundAssignmentExpression x);

    void performActionOnContinueExpression(ContinueExpression x);

    void performActionOnBreakExpression(BreakExpression x);

    void performActionOnReturnExpression(ReturnExpression x);

    void performActionOnGroupedExpression(GroupedExpression x);

    void performActionOnEnumeratedArrayExpression(EnumeratedArrayExpression x);

    void performActionOnRepeatedArrayExpression(RepeatedArrayExpression x);

    void performActionOnTupleExpression(TupleExpression x);

    void performActionOnPathInExpression(PathInExpression x);

    void performActionOnTupleStructExpression(TupleStructExpression x);

    void performActionOnUnitStructExpression(UnitStructExpression x);

    void performActionOnFieldStructExpression(StructStructExpression x);

    void performActionOnEnumVariantFieldless(EnumVariantFieldless x);

    void performActionOnEnumVariantTuple(EnumVariantTuple x);

    void performActionOnClosureExpression(ClosureExpression x);

    void performActionOnEnumVariantStruct(EnumVariantStruct x);

    void performActionOnInfiniteLoop(InfiniteLoopExpression x);

    void performActionOnPredicatePatternLoopExpression(PredicatePatternLoopExpression x);

    void performActionOnIteratorLoopExpression(IteratorLoopExpression x);

    void performActionOnIfExpression(IfExpression x);

    void performActionOnMatchExpression(MatchExpression x);

    void performActionOnMatchArm(MatchArm x);

    void performActionOnExpressionStatement(ExpressionStatement x);

    void performActionOnPrimitiveRustType(PrimitiveRustType x);

    void performActionOnSchemaRustType(SchemaRustType x);

    void performActionOnLetStatement(LetStatement x);

    void performActionOnIdentPattern(IdentPattern x);

    void performActionOnSchemaVarPattern(SchemaVarPattern x);

    void performActionOnLiteralPattern(LiteralPattern x);

    void performActionOnAltPattern(AltPattern x);

    void performActionOnWildCardPattern(WildCardPattern x);

    void performActionOnRangepattern(RangePattern x);

    void performActionOnReferenceRustType(ReferenceRustType x);

    void performActionOnBinaryExpression(BinaryExpression x);

    void performActionOnBinaryOperator(BinaryExpression.Operator x);

    void performActionOnUnaryExpression(UnaryExpression x);

    void performActionOnUnaryOperator(UnaryExpression.Operator x);

    void performActionOnBindingPattern(BindingPattern x);

    void performActionOnLetExpression(LetExpression x);

    void performActionOnTypeOf(TypeOf x);

    void performActionOnProgramFunction(ProgramFunction x);

    void performActionOnFunctionBodyExpression(FunctionBodyExpression x);

    void performActionOnFunctionFrame(FunctionFrame x);

    void performActionOnLoopInvariant(LoopSpecification x);

    void performActionOnProgramMetaConstruct(ProgramTransformer x);

    void performActionOnLoopScope(LoopScope x);

    void performActionOnSortRustType(SortRustType x);

    void performActionOnLitPatExpr(LitPatExpr x);
}
