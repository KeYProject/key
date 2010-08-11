// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.metaconstruct.ProgramMetaConstruct;
import de.uka.ilkd.key.rule.soundness.ProgramSVProxy;
import de.uka.ilkd.key.rule.soundness.ProgramSVSkolem;
import de.uka.ilkd.key.speclang.LoopInvariant;

/**
 * This class is implemented by visitors/walkers.
 * Each AST node implements a visit(Visitor) method that
 * calls the  doActionAt<NodeType> method. Similar to the pretty print
 * mechanism.
 */
public interface Visitor {

     void performActionOnAbstractProgramElement
	(AbstractProgramElement x);

     void performActionOnProgramElementName(
			    ProgramElementName x);

     void performActionOnProgramVariable(
			    ProgramVariable x);

     void performActionOnIProgramVariable(
             IProgramVariable x);

     void performActionOnSchemaVariable(
			    SchemaVariable x);
    
     void performActionOnProgramMethod(
			    ProgramMethod x);

     void performActionOnProgramMetaConstruct(
			    ProgramMetaConstruct x);

     void performActionOnContextStatementBlock(
			    ContextStatementBlock x);

     void performActionOnIntLiteral(IntLiteral x); 

     void performActionOnBooleanLiteral(BooleanLiteral x); 

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
     
     void performActionOnSetAssignment(SetAssignment x);

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

     void performActionOnUnsignedShiftRightAssignment 
	(UnsignedShiftRightAssignment x); 

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

     void performActionOnMethodReference(MethodReference x); 

     void performActionOnFieldReference(FieldReference x); 

     void performActionOnSchematicFieldReference(SchematicFieldReference x); 

     void performActionOnVariableReference(VariableReference x); 

     void performActionOnMethod(ProgramMethod x); 

     void performActionOnSuperConstructorReference(SuperConstructorReference x); 

     void performActionOnExecutionContext(ExecutionContext x); 

     void performActionOnConstructorDeclaration(ConstructorDeclaration x); 

     void performActionOnThisConstructorReference(ThisConstructorReference x); 

     void performActionOnSuperReference(SuperReference x); 

     void performActionOnThisReference(ThisReference x); 
     
//     void performActionOnCurrentMemoryAreaReference(CurrentMemoryAreaReference x); 

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

     void performActionOnProgramSVSkolem(ProgramSVSkolem x); 

     void performActionOnProgramSVProxy(ProgramSVProxy x);

     void performActionOnAssert(Assert assert1);

    void performActionOnProgramConstant(ProgramConstant constant);

    void performActionOnLocationVariable(LocationVariable variable); 
    
    void performActionOnLoopInvariant(LoopInvariant x);

    void performActionOnMemoryAreaEC(MemoryAreaEC memoryAreaEC);

    void performActionOnRuntimeInstanceEC(RuntimeInstanceEC runtimeInstanceEC);
}
