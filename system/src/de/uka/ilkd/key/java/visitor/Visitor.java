// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.java.visitor;

import de.uka.ilkd.key.java.Comment;
import de.uka.ilkd.key.java.CompilationUnit;
import de.uka.ilkd.key.java.ContextStatementBlock;
import de.uka.ilkd.key.java.Import;
import de.uka.ilkd.key.java.PackageSpecification;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.declaration.ArrayDeclaration;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.ClassInitializer;
import de.uka.ilkd.key.java.declaration.ConstructorDeclaration;
import de.uka.ilkd.key.java.declaration.Extends;
import de.uka.ilkd.key.java.declaration.FieldDeclaration;
import de.uka.ilkd.key.java.declaration.FieldSpecification;
import de.uka.ilkd.key.java.declaration.Implements;
import de.uka.ilkd.key.java.declaration.ImplicitFieldSpecification;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.MethodDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.SuperArrayDeclaration;
import de.uka.ilkd.key.java.declaration.Throws;
import de.uka.ilkd.key.java.declaration.VariableDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.CharLiteral;
import de.uka.ilkd.key.java.expression.literal.DoubleLiteral;
import de.uka.ilkd.key.java.expression.literal.EmptySeqLiteral;
import de.uka.ilkd.key.java.expression.literal.EmptySetLiteral;
import de.uka.ilkd.key.java.expression.literal.FloatLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.literal.LongLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.java.expression.operator.BinaryAnd;
import de.uka.ilkd.key.java.expression.operator.BinaryAndAssignment;
import de.uka.ilkd.key.java.expression.operator.BinaryNot;
import de.uka.ilkd.key.java.expression.operator.BinaryOr;
import de.uka.ilkd.key.java.expression.operator.BinaryOrAssignment;
import de.uka.ilkd.key.java.expression.operator.BinaryXOr;
import de.uka.ilkd.key.java.expression.operator.BinaryXOrAssignment;
import de.uka.ilkd.key.java.expression.operator.Conditional;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.DLEmbeddedExpression;
import de.uka.ilkd.key.java.expression.operator.Divide;
import de.uka.ilkd.key.java.expression.operator.DivideAssignment;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.expression.operator.ExactInstanceof;
import de.uka.ilkd.key.java.expression.operator.GreaterOrEquals;
import de.uka.ilkd.key.java.expression.operator.GreaterThan;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.java.expression.operator.Intersect;
import de.uka.ilkd.key.java.expression.operator.LessOrEquals;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.expression.operator.LogicalAnd;
import de.uka.ilkd.key.java.expression.operator.LogicalNot;
import de.uka.ilkd.key.java.expression.operator.LogicalOr;
import de.uka.ilkd.key.java.expression.operator.Minus;
import de.uka.ilkd.key.java.expression.operator.MinusAssignment;
import de.uka.ilkd.key.java.expression.operator.Modulo;
import de.uka.ilkd.key.java.expression.operator.ModuloAssignment;
import de.uka.ilkd.key.java.expression.operator.Negative;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.expression.operator.NotEquals;
import de.uka.ilkd.key.java.expression.operator.Plus;
import de.uka.ilkd.key.java.expression.operator.PlusAssignment;
import de.uka.ilkd.key.java.expression.operator.Positive;
import de.uka.ilkd.key.java.expression.operator.PostDecrement;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.java.expression.operator.PreDecrement;
import de.uka.ilkd.key.java.expression.operator.PreIncrement;
import de.uka.ilkd.key.java.expression.operator.ShiftLeft;
import de.uka.ilkd.key.java.expression.operator.ShiftLeftAssignment;
import de.uka.ilkd.key.java.expression.operator.ShiftRight;
import de.uka.ilkd.key.java.expression.operator.ShiftRightAssignment;
import de.uka.ilkd.key.java.expression.operator.Times;
import de.uka.ilkd.key.java.expression.operator.TimesAssignment;
import de.uka.ilkd.key.java.expression.operator.TypeCast;
import de.uka.ilkd.key.java.expression.operator.UnsignedShiftRight;
import de.uka.ilkd.key.java.expression.operator.UnsignedShiftRightAssignment;
import de.uka.ilkd.key.java.expression.operator.adt.AllFields;
import de.uka.ilkd.key.java.expression.operator.adt.AllObjects;
import de.uka.ilkd.key.java.expression.operator.adt.SeqConcat;
import de.uka.ilkd.key.java.expression.operator.adt.SeqGet;
import de.uka.ilkd.key.java.expression.operator.adt.SeqIndexOf;
import de.uka.ilkd.key.java.expression.operator.adt.SeqLength;
import de.uka.ilkd.key.java.expression.operator.adt.SeqReverse;
import de.uka.ilkd.key.java.expression.operator.adt.SeqSingleton;
import de.uka.ilkd.key.java.expression.operator.adt.SeqSub;
import de.uka.ilkd.key.java.expression.operator.adt.SetMinus;
import de.uka.ilkd.key.java.expression.operator.adt.SetUnion;
import de.uka.ilkd.key.java.expression.operator.adt.Singleton;
import de.uka.ilkd.key.java.reference.ArrayLengthReference;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MetaClassReference;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.PackageReference;
import de.uka.ilkd.key.java.reference.SchematicFieldReference;
import de.uka.ilkd.key.java.reference.SuperConstructorReference;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisConstructorReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.reference.VariableReference;
import de.uka.ilkd.key.java.statement.Assert;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.Case;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.CatchAllStatement;
import de.uka.ilkd.key.java.statement.Continue;
import de.uka.ilkd.key.java.statement.Default;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.Finally;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.ForUpdates;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopInit;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.java.statement.Switch;
import de.uka.ilkd.key.java.statement.SynchronizedBlock;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.java.statement.TransactionStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.speclang.BlockContract;
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
	    IProgramMethod x);

    void performActionOnProgramMetaConstruct(
	    ProgramTransformer x);

    void performActionOnContextStatementBlock(
	    ContextStatementBlock x);

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

    void performActionOnLoopInvariant(LoopInvariant x);
    
    void performActionOnBlockContract(BlockContract x);

    void performActionOnSeqLength(SeqLength seqLength);

    void performActionOnSeqGet(SeqGet seqGet);
    
    void performActionOnTransactionStatement(TransactionStatement transSt);

}
