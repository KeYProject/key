// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util.joinrule;

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
import de.uka.ilkd.key.java.expression.literal.EmptyMapLiteral;
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
import de.uka.ilkd.key.java.reference.TypeRef;
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
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramConstant;
import de.uka.ilkd.key.logic.op.ProgramMethod;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.AbstractProgramElement;
import de.uka.ilkd.key.rule.metaconstruct.ProgramTransformer;
import de.uka.ilkd.key.speclang.BlockContract;
import de.uka.ilkd.key.speclang.LoopInvariant;

/**
 * TODO: Document.
 * 
 * This class is implemented by visitors/walkers. Each AST node implements a
 * visit(Visitor) method that calls the doActionAt<NodeType> method. Similar to
 * the pretty print mechanism.
 *
 * @see Visitor
 * @author Dominic Scheurer
 */
public interface SimultaneousVisitor {

    public void visit(AbstractProgramElement x1, AbstractProgramElement x2);

    public void visit(ArrayDeclaration x1, ArrayDeclaration x2);

    public void visit(ArrayInitializer x1, ArrayInitializer x2);

    public void visit(ArrayLengthReference x1, ArrayLengthReference x2);

    public void visit(ArrayReference x1, ArrayReference x2);

    public void visit(Assert x1, Assert x2);

    public void visit(BinaryAnd x1, BinaryAnd x2);

    public void visit(BinaryAndAssignment x1, BinaryAndAssignment x2);

    public void visit(BinaryNot x1, BinaryNot x2);

    public void visit(BinaryOr x1, BinaryOr x2);

    public void visit(BinaryOrAssignment x1, BinaryOrAssignment x2);

    public void visit(BinaryXOr x1, BinaryXOr x2);

    public void visit(BinaryXOrAssignment x1, BinaryXOrAssignment x2);

    public void visit(BooleanLiteral x1, BooleanLiteral x2);

    public void visit(EmptySetLiteral x1, EmptySetLiteral x2);

    public void visit(Singleton x1, Singleton x2);

    public void visit(SetUnion x1, SetUnion x2);

    public void visit(Intersect x1, Intersect x2);

    public void visit(SetMinus x1, SetMinus x2);

    public void visit(AllFields x1, AllFields x2);

    public void visit(AllObjects x1, AllObjects x2);

    public void visit(EmptySeqLiteral x1, EmptySeqLiteral x2);

    public void visit(SeqSingleton x1, SeqSingleton x2);

    public void visit(SeqConcat x1, SeqConcat x2);

    public void visit(SeqSub x1, SeqSub x2);

    public void visit(SeqReverse x1, SeqReverse x2);

    public void visit(DLEmbeddedExpression x1, DLEmbeddedExpression x2);

    public void visit(SeqIndexOf x1, SeqIndexOf x2);

    public void visit(SeqGet x1, SeqGet x2);

    public void visit(SeqLength x1, SeqLength x2);

    public void visit(Break x1, Break x2);

    public void visit(Case x1, Case x2);

    public void visit(Catch x1, Catch x2);

    public void visit(CatchAllStatement x1, CatchAllStatement x2);

    public void visit(CharLiteral x1, CharLiteral x2);

    public void visit(ClassDeclaration x1, ClassDeclaration x2);

    public void visit(ClassInitializer x1, ClassInitializer x2);

    public void visit(Comment x1, Comment x2);

    public void visit(CompilationUnit x1, CompilationUnit x2);

    public void visit(Conditional x1, Conditional x2);

    public void visit(ConstructorDeclaration x1, ConstructorDeclaration x2);

    public void visit(ContextStatementBlock x1, ContextStatementBlock x2);

    public void visit(Continue x1, Continue x2);

    public void visit(CopyAssignment x1, CopyAssignment x2);

    public void visit(Default x1, Default x2);

    public void visit(Divide x1, Divide x2);

    public void visit(DivideAssignment x1, DivideAssignment x2);

    public void visit(Do x1, Do x2);

    public void visit(DoubleLiteral x1, DoubleLiteral x2);

    public void visit(Else x1, Else x2);

    public void visit(EmptyStatement x1, EmptyStatement x2);

    public void visit(Equals x1, Equals x2);

    public void visit(ExactInstanceof x1, ExactInstanceof x2);

    public void visit(ExecutionContext x1, ExecutionContext x2);

    public void visit(Extends x1, Extends x2);

    public void visit(EnhancedFor x1, EnhancedFor x2);

    public void visit(FieldDeclaration x1, FieldDeclaration x2);

    public void visit(FieldReference x1, FieldReference x2);

    public void visit(FieldSpecification x1, FieldSpecification x2);

    public void visit(Finally x1, Finally x2);

    public void visit(FloatLiteral x1, FloatLiteral x2);

    public void visit(For x1, For x2);

    public void visit(ForUpdates x1, ForUpdates x2);

    public void visit(GreaterOrEquals x1, GreaterOrEquals x2);

    public void visit(GreaterThan x1, GreaterThan x2);

    public void visit(Guard x1, Guard x2);

    public void visit(If x1, If x2);

    public void visit(Implements x1, Implements x2);

    public void visit(ImplicitFieldSpecification x1,
            ImplicitFieldSpecification x2);

    public void visit(Import x1, Import x2);

    public void visit(Instanceof x1, Instanceof x2);

    public void visit(InterfaceDeclaration x1, InterfaceDeclaration x2);

    public void visit(IntLiteral x1, IntLiteral x2);

    public void visit(LabeledStatement x1, LabeledStatement x2);

    public void visit(LessOrEquals x1, LessOrEquals x2);

    public void visit(LessThan x1, LessThan x2);

    public void visit(LocalVariableDeclaration x1, LocalVariableDeclaration x2);

    public void visit(LocationVariable x1, LocationVariable x2);

    public void visit(LogicalAnd x1, LogicalAnd x2);

    public void visit(LogicalNot x1, LogicalNot x2);

    public void visit(LogicalOr x1, LogicalOr x2);

    public void visit(LongLiteral x1, LongLiteral x2);

    public void visit(LoopInit x1, LoopInit x2);

    public void visit(MetaClassReference x1, MetaClassReference x2);

    public void visit(MethodBodyStatement x1, MethodBodyStatement x2);

    public void visit(MethodDeclaration x1, MethodDeclaration x2);

    public void visit(MethodFrame x1, MethodFrame x2);

    public void visit(MethodReference x1, MethodReference x2);

    public void visit(Minus x1, Minus x2);

    public void visit(MinusAssignment x1, MinusAssignment x2);

    public void visit(Modifier x1, Modifier x2);

    public void visit(Modulo x1, Modulo x2);

    public void visit(ModuloAssignment x1, ModuloAssignment x2);

    public void visit(Negative x1, Negative x2);

    public void visit(New x1, New x2);

    public void visit(NewArray x1, NewArray x2);

    public void visit(NotEquals x1, NotEquals x2);

    public void visit(NullLiteral x1, NullLiteral x2);

    public void visit(PackageReference x1, PackageReference x2);

    public void visit(PackageSpecification x1, PackageSpecification x2);

    public void visit(ParameterDeclaration x1, ParameterDeclaration x2);

    public void visit(ParenthesizedExpression x1, ParenthesizedExpression x2);

    public void visit(PassiveExpression x1, PassiveExpression x2);

    public void visit(Plus x1, Plus x2);

    public void visit(PlusAssignment x1, PlusAssignment x2);

    public void visit(Positive x1, Positive x2);

    public void visit(PostDecrement x1, PostDecrement x2);

    public void visit(PostIncrement x1, PostIncrement x2);

    public void visit(PreDecrement x1, PreDecrement x2);

    public void visit(PreIncrement x1, PreIncrement x2);

    public void visit(ProgramConstant x1, ProgramConstant x2);

    public void visit(ProgramElementName x1, ProgramElementName x2);

    public void visit(ProgramTransformer x1, ProgramTransformer x2);

    public void visit(ProgramMethod x1, ProgramMethod x2);

    public void visit(ProgramVariable x1, ProgramVariable x2);

    public void visit(IProgramVariable x1, IProgramVariable x2);

    public void visit(Return x1, Return x2);

    public void visit(SchematicFieldReference x1, SchematicFieldReference x2);

    public void visit(SchemaVariable x1, SchemaVariable x2);

    public void visit(ShiftLeft x1, ShiftLeft x2);

    public void visit(ShiftLeftAssignment x1, ShiftLeftAssignment x2);

    public void visit(ShiftRight x1, ShiftRight x2);

    public void visit(ShiftRightAssignment x1, ShiftRightAssignment x2);

    public void visit(StatementBlock x1, StatementBlock x2);

    public void visit(StringLiteral x1, StringLiteral x2);

    public void visit(SuperArrayDeclaration x1, SuperArrayDeclaration x2);

    public void visit(SuperConstructorReference x1, SuperConstructorReference x2);

    public void visit(SuperReference x1, SuperReference x2);

    public void visit(Switch x1, Switch x2);

    public void visit(SynchronizedBlock x1, SynchronizedBlock x2);

    public void visit(Then x1, Then x2);

    public void visit(ThisConstructorReference x1, ThisConstructorReference x2);

    public void visit(ThisReference x1, ThisReference x2);

    public void visit(Throw x1, Throw x2);

    public void visit(Throws x1, Throws x2);

    public void visit(Times x1, Times x2);

    public void visit(TimesAssignment x1, TimesAssignment x2);

    public void visit(Try x1, Try x2);

    public void visit(TypeCast x1, TypeCast x2);

    public void visit(TypeRef x1, TypeRef x2);

    public void visit(UnsignedShiftRight x1, UnsignedShiftRight x2);

    public void visit(UnsignedShiftRightAssignment x1,
            UnsignedShiftRightAssignment x2);

    public void visit(VariableDeclaration x1, VariableDeclaration x2);

    public void visit(VariableReference x1, VariableReference x2);

    public void visit(VariableSpecification x1, VariableSpecification x2);

    public void visit(While x1, While x2);

    public void visit(LoopInvariant x);

    public void visit(BlockContract x);

    public void visit(TransactionStatement x1, TransactionStatement x2);

    public void visit(EmptyMapLiteral x1, EmptyMapLiteral x2);

}
