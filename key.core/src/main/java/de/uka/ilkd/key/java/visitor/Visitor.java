/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.ccatch.*;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.java.ast.expression.ArrayInitializer;
import de.uka.ilkd.key.java.ast.expression.Assignment;
import de.uka.ilkd.key.java.ast.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.ast.expression.PassiveExpression;
import de.uka.ilkd.key.java.ast.expression.literal.*;
import de.uka.ilkd.key.java.ast.expression.operator.*;
import de.uka.ilkd.key.java.ast.reference.*;
import de.uka.ilkd.key.java.ast.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.LoopContract;
import de.uka.ilkd.key.speclang.LoopSpecification;
import de.uka.ilkd.key.speclang.MergeContract;

import org.key_project.logic.op.sv.SchemaVariable;

/**
 * This class is implemented by visitors/walkers. Each AST node implements a visit(Visitor) method
 * that calls the doActionAt<NodeType> method. Similar to the pretty print mechanism.
 */
public interface Visitor {

    void performActionOnAbstractProgramElement(AbstractProgramElement x);

    void performActionOnProgramElementName(ProgramElementName x);

    void performActionOnProgramVariable(ProgramVariable x);

    void performActionOnSchemaVariable(SchemaVariable x);

    void performActionOnProgramMethod(IProgramMethod x);

    void performActionOnProgramMetaConstruct(ProgramTransformer x);

    void performActionOnContextStatementBlock(ContextStatementBlock x);

    void performActionOnIntLiteral(IntLiteral x);

    void performActionOnRealLiteral(RealLiteral realLiteral);

    void performActionOnBooleanLiteral(BooleanLiteral x);

    void performActionOnEmptySetLiteral(EmptySetLiteral x);

    void performActionOnEmptySeqLiteral(EmptySeqLiteral x);

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

    void performActionOnSetStatement(SetStatement x);

    void performActionOnConditional(Conditional x);

    void performActionOnNewArray(NewArray x);

    void performActionOnInstanceof(Instanceof x);

    void performActionOnExactInstanceof(ExactInstanceof x);

    void performActionOnNew(New x);

    void performActionOnTypeCast(TypeCast x);

    void performActionOnArrayReference(ArrayReference x);

    void performActionOnMetaClassReference(MetaClassReference x);

    void performActionOnMergePointStatement(MergePointStatement x);

    void performActionOnMethodReference(MethodReference x);

    void performActionOnFieldReference(FieldReference x);

    void performActionOnSchematicFieldReference(SchematicFieldReference x);

    void performActionOnVariableReference(VariableReference x);

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
     * @param oldBlock
     *        the old block
     * @param newBlock
     *        the new block
     */
    void performActionOnBlockContract(final StatementBlock oldBlock, final StatementBlock newBlock);

    /**
     * Adds block contract for new statement block to block contract of old block statement.
     *
     * @param oldBlock
     *        the old block
     * @param newBlock
     *        the new block
     */
    void performActionOnLoopContract(final StatementBlock oldBlock, final StatementBlock newBlock);

    /**
     * Adds loop contract for new loop statement to loop contract of old loop statement.
     *
     * @param oldLoop
     *        the old loop statement
     * @param newLoop
     *        the new loop statement
     */
    void performActionOnLoopContract(final LoopStatement oldLoop, final LoopStatement newLoop);

    void performActionOnMergeContract(MergeContract x);

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
     * @param jmlAssert
     *        the statement to perform the action on.
     */
    void performActionOnJmlAssert(JmlAssert jmlAssert);

    void performActionOnSubtype(Subtype subtype);

    void performActionOnBinaryOperator(BinaryOperator op);

    void performActionOnUnaryOperator(UnaryOperator op);

    void performActionOnLogicFunctionalOperator(LogicFunctionalOperator op);

    void performActionOnAssignment(Assignment assignment);
}
