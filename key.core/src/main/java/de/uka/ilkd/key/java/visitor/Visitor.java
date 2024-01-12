/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.expression.operator.adt.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.speclang.MergeContract;

/**
 * This class is implemented by visitors/walkers. Each AST node implements a visit(Visitor) method
 * that calls the doActionAt<NodeType> method. Similar to the pretty print mechanism.
 */
public interface Visitor {

    void performActionOnAbstractProgramElement(AbstractProgramElement x);

    void performActionOnProgramElementName(ProgramElementName x);

    void performActionOnProgramVariable(ProgramVariable x);

    void performActionOnIProgramVariable(IProgramVariable x);

    void performActionOnSchemaVariable(SchemaVariable x);

    void performActionOnProgramMethod(IProgramMethod x);

    void performActionOnProgramMetaConstruct(ProgramTransformer x);

    void performActionOnContextStatementBlock(ContextStatementBlock x);

    void performActionOnIntLiteral(IntLiteral x);

    void performActionOnBooleanLiteral(BooleanLiteral x);

    void performActionOnEmptySetLiteral(EmptySetLiteral x);

    void performActionOnSingleton(Singleton x);

    void performActionOnSetUnion(SetUnion x);

    void performActionOnIntersect(Intersect x);

    void performActionOnSetMinus(SetMinus x);

    void performActionOnAllFields(AllFields x);

    void performActionOnAllObjects(AllObjects allObjects);

    void performActionOnEmptySeqLiteral(EmptySeqLiteral x);

    void performActionOnSeqSingleton(SeqSingleton x);

    void performActionOnSeqConcat(SeqConcat x);

    void performActionOnSeqIndexOf(SeqIndexOf x);

    void performActionOnSeqSub(SeqSub x);

    void performActionOnSeqReverse(SeqReverse x);

    void performActionOnDLEmbeddedExpression(DLEmbeddedExpression x);

    void performActionOnStringLiteral(StringLiteral x);

    void performActionOnNullLiteral(NullLiteral x);

    void performActionOnCharLiteral(CharLiteral x);

    void performActionOnDoubleLiteral(DoubleLiteral x);

    void performActionOnLongLiteral(LongLiteral x);

    void performActionOnFloatLiteral(FloatLiteral x);

    void performActionOnPackageSpecification(PackageSpecification x);

    void performActionOnTypeReference(TypeReference x);

    void performActionOnPackageReference(PackageReference x);

    void performActionOnThrows(Throws x);

    void performActionOnArrayInitializer(ArrayInitializer x);

    void performActionOnCompilationUnit(CompilationUnit x);

    void performActionOnArrayDeclaration(ArrayDeclaration x);

    void performActionOnSuperArrayDeclaration(SuperArrayDeclaration x);

    void performActionOnClassDeclaration(ClassDeclaration x);

    void performActionOnInterfaceDeclaration(InterfaceDeclaration x);

    void performActionOnFieldDeclaration(FieldDeclaration x);

    void performActionOnLocalVariableDeclaration(LocalVariableDeclaration x);

    void performActionOnVariableDeclaration(VariableDeclaration x);

    void performActionOnParameterDeclaration(ParameterDeclaration x);

    void performActionOnMethodDeclaration(MethodDeclaration x);

    void performActionOnClassInitializer(ClassInitializer x);

    void performActionOnStatementBlock(StatementBlock x);

    void performActionOnBreak(Break x);

    void performActionOnContinue(Continue x);

    void performActionOnReturn(Return x);

    void performActionOnThrow(Throw x);

    void performActionOnDo(Do x);

    void performActionOnFor(For x);

    void performActionOnEnhancedFor(EnhancedFor x);

    void performActionOnWhile(While x);

    void performActionOnIf(If x);

    void performActionOnSwitch(Switch x);

    void performActionOnTry(Try x);

    void performActionOnLabeledStatement(LabeledStatement x);

    void performActionOnMethodFrame(MethodFrame x);

    void performActionOnMethodBodyStatement(MethodBodyStatement x);

    void performActionOnCatchAllStatement(CatchAllStatement x);

    void performActionOnSynchronizedBlock(SynchronizedBlock x);

    void performActionOnLoopScopeBlock(LoopScopeBlock x);

    void performActionOnImport(Import x);

    void performActionOnExtends(Extends x);

    void performActionOnImplements(Implements x);

    void performActionOnVariableSpecification(VariableSpecification x);

    void performActionOnFieldSpecification(FieldSpecification x);

    void performActionOnImplicitFieldSpecification(ImplicitFieldSpecification x);

    void performActionOnBinaryAnd(BinaryAnd x);

    void performActionOnBinaryAndAssignment(BinaryAndAssignment x);

    void performActionOnBinaryOrAssignment(BinaryOrAssignment x);

    void performActionOnBinaryXOrAssignment(BinaryXOrAssignment x);

    void performActionOnCopyAssignment(CopyAssignment x);

    void performActionOnDivideAssignment(DivideAssignment x);

    void performActionOnMinusAssignment(MinusAssignment x);

    void performActionOnModuloAssignment(ModuloAssignment x);

    void performActionOnPlusAssignment(PlusAssignment x);

    void performActionOnPostDecrement(PostDecrement x);

    void performActionOnPostIncrement(PostIncrement x);

    void performActionOnPreDecrement(PreDecrement x);

    void performActionOnPreIncrement(PreIncrement x);

    void performActionOnShiftLeftAssignment(ShiftLeftAssignment x);

    void performActionOnShiftRightAssignment(ShiftRightAssignment x);

    void performActionOnTimesAssignment(TimesAssignment x);

    void performActionOnUnsignedShiftRightAssignment(UnsignedShiftRightAssignment x);

    void performActionOnBinaryNot(BinaryNot x);

    void performActionOnBinaryOr(BinaryOr x);

    void performActionOnBinaryXOr(BinaryXOr x);

    void performActionOnConditional(Conditional x);

    void performActionOnDivide(Divide x);

    void performActionOnEquals(Equals x);

    void performActionOnGreaterOrEquals(GreaterOrEquals x);

    void performActionOnGreaterThan(GreaterThan x);

    void performActionOnLessOrEquals(LessOrEquals x);

    void performActionOnLessThan(LessThan x);

    void performActionOnNotEquals(NotEquals x);

    void performActionOnNewArray(NewArray x);

    void performActionOnInstanceof(Instanceof x);

    void performActionOnExactInstanceof(ExactInstanceof x);

    void performActionOnNew(New x);

    void performActionOnTypeCast(TypeCast x);

    void performActionOnLogicalAnd(LogicalAnd x);

    void performActionOnLogicalNot(LogicalNot x);

    void performActionOnLogicalOr(LogicalOr x);

    void performActionOnMinus(Minus x);

    void performActionOnModulo(Modulo x);

    void performActionOnNegative(Negative x);

    void performActionOnPlus(Plus x);

    void performActionOnPositive(Positive x);

    void performActionOnShiftLeft(ShiftLeft x);

    void performActionOnShiftRight(ShiftRight x);

    void performActionOnTimes(Times x);

    void performActionOnUnsignedShiftRight(UnsignedShiftRight x);

    void performActionOnArrayReference(ArrayReference x);

    void performActionOnMetaClassReference(MetaClassReference x);

    void performActionOnMergePointStatement(MergePointStatement x);

    void performActionOnMethodReference(MethodReference x);

    void performActionOnFieldReference(FieldReference x);

    void performActionOnSchematicFieldReference(SchematicFieldReference x);

    void performActionOnVariableReference(VariableReference x);

    void performActionOnMethod(IProgramMethod x);

    void performActionOnSuperConstructorReference(SuperConstructorReference x);

    void performActionOnExecutionContext(ExecutionContext x);

    void performActionOnConstructorDeclaration(ConstructorDeclaration x);

    void performActionOnThisConstructorReference(ThisConstructorReference x);

    void performActionOnSuperReference(SuperReference x);

    void performActionOnThisReference(ThisReference x);

    void performActionOnArrayLengthReference(ArrayLengthReference x);

    void performActionOnThen(Then x);

    void performActionOnElse(Else x);

    void performActionOnCase(Case x);

    void performActionOnCatch(Catch x);

    void performActionOnDefault(Default x);

    void performActionOnFinally(Finally x);

    void performActionOnModifier(Modifier x);

    void performActionOnEmptyStatement(EmptyStatement x);

    void performActionOnComment(Comment x);

    void performActionOnParenthesizedExpression(ParenthesizedExpression x);

    void performActionOnPassiveExpression(PassiveExpression x);

    void performActionOnForUpdates(ForUpdates x);

    void performActionOnGuard(Guard x);

    void performActionOnLoopInit(LoopInit x);

    void performActionOnAssert(Assert assert1);

    void performActionOnProgramConstant(ProgramConstant constant);

    void performActionOnLocationVariable(LocationVariable variable);

    void performActionOnLoopInvariant(LoopSpecification x);

    void performActionOnBlockContract(BlockContract x);

    void performActionOnLoopContract(LoopContract x);

    /**
     * Adds block contract for new statement block to block contract of old block statement.
     *
     * @param oldBlock the old block
     * @param newBlock the new block
     */
    void performActionOnBlockContract(final StatementBlock oldBlock, final StatementBlock newBlock);

    /**
     * Adds block contract for new statement block to block contract of old block statement.
     *
     * @param oldBlock the old block
     * @param newBlock the new block
     */
    void performActionOnLoopContract(final StatementBlock oldBlock, final StatementBlock newBlock);

    /**
     * Adds loop contract for new loop statement to loop contract of old loop statement.
     *
     * @param oldLoop the old loop statement
     * @param newLoop the new loop statement
     */
    void performActionOnLoopContract(final LoopStatement oldLoop, final LoopStatement newLoop);

    void performActionOnMergeContract(MergeContract x);

    void performActionOnSeqLength(SeqLength seqLength);

    void performActionOnSeqGet(SeqGet seqGet);

    void performActionOnTransactionStatement(TransactionStatement transSt);

    void performActionOnEmptyMapLiteral(EmptyMapLiteral aThis);

    void performActionOnExec(Exec exec);

    void performActionOnCcatch(Ccatch ccatch);

    void performActionOnCcatchReturnParameterDeclaration(
            CcatchReturnParameterDeclaration ccatchReturnParameterDeclaration);

    void performActionOnCcatchReturnValParameterDeclaration(
            CcatchReturnValParameterDeclaration ccatchReturnValParameterDeclaration);

    void performActionOnCcatchContinueParameterDeclaration(
            CcatchContinueParameterDeclaration ccatchContinueParameterDeclaration);

    void performActionOnCcatchBreakParameterDeclaration(
            CcatchBreakParameterDeclaration ccatchBreakParameterDeclaration);

    void performActionOnCcatchBreakLabelParameterDeclaration(
            CcatchBreakLabelParameterDeclaration ccatchBreakLabelParameterDeclaration);

    void performActionOnCCcatchContinueLabelParameterDeclaration(
            CcatchContinueLabelParameterDeclaration ccatchContinueLabelParameterDeclaration);

    void performActionOnCcatchContinueWildcardParameterDeclaration(
            CcatchContinueWildcardParameterDeclaration ccatchContinueWildcardParameterDeclaration);

    void performActionOnCcatchBreakWildcardParameterDeclaration(
            CcatchBreakWildcardParameterDeclaration ccatchBreakWildcardParameterDeclaration);

    /**
     * Performs action on JML assert statement.
     *
     * @param jmlAssert the statement to perform the action on.
     */
    void performActionOnJmlAssert(JmlAssert jmlAssert);

    /**
     * Performs action on the condition of a JML assert statement.
     *
     * Note: if you don't extend JavaASTVisitor or something else that calls this methode for you,
     * you have to call it yourself, e.g. in {@link #performActionOnJmlAssert} if needed.
     *
     * @param cond the condition to perform an action on (may be {@code null} if the JML assert
     *        wasn't finished)
     */
    void performActionOnJmlAssertCondition(final Term cond);
}
