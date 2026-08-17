package org.key_project.java.ast.visitor;

import org.key_project.java.ast.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;

public interface Visitor<R> {

    R visit(CompilationUnit n);

    R visit(ContextStatementBlock n);

    R visit(Import n);

    R visit(StatementBlock n);

    R visit(ArrayDeclaration n);

    R visit(ClassDeclaration n);

    R visit(ClassInitializer n);

    R visit(ConstructorDeclaration n);

    R visit(EnumClassDeclaration n);

    R visit(Extends n);

    R visit(FieldDeclaration n);

    R visit(FieldSpecification n);

    R visit(Implements n);

    R visit(InterfaceDeclaration n);

    R visit(LocalVariableDeclaration n);

    R visit(MethodDeclaration n);

    R visit(ParameterDeclaration n);

    R visit(SuperArrayDeclaration n);

    R visit(Throws n);

    R visit(VariableSpecification n);

    R visit(AnnotationUseSpecification n);

    R visit(ArrayInitializer n);

    R visit(ParenthesizedExpression n);

    R visit(PassiveExpression n);

    R visit(BooleanLiteral n);

    R visit(DoubleLiteral n);

    R visit(FloatLiteral n);

    R visit(FreeLiteral n);

    R visit(IntLiteral n);

    R visit(LongLiteral n);

    R visit(RealLiteral n);

    R visit(StringLiteral n);

    R visit(Assignment n);

    R visit(BinaryOperator n);

    R visit(UnaryOperator n);

    R visit(LogicalFunctionOperator n);

    R visit(Conditional n);

    R visit(DLEmbeddedExpression n);

    R visit(ExactInstanceof n);

    R visit(Instanceof n);

    R visit(New n);

    R visit(NewArray n);

    R visit(TypeCast n);

    R visit(ArrayLengthReference n);

    R visit(ArrayReference n);

    R visit(ExecutionContext n);

    R visit(FieldReference n);

    R visit(MetaClassReference n);

    R visit(MethodReference n);

    R visit(PackageReference n);

    R visit(SchemaTypeReference n);

    R visit(SchematicFieldReference n);

    R visit(SuperConstructorReference n);

    R visit(SuperReference n);

    R visit(ThisConstructorReference n);

    R visit(ThisReference n);

    R visit(TypeRef n);

    R visit(VariableReference n);

    R visit(Assert n);

    R visit(Break n);

    R visit(Case n);

    R visit(Default n);

    R visit(SingleCatch n);

    R visit(CatchAllStatement n);

    R visit(Ccatch n);

    R visit(Continue n);

    R visit(Do n);

    R visit(EmptyStatement n);

    R visit(EnhancedFor n);

    R visit(Exec n);

    R visit(For n);

    R visit(ForUpdates n);

    R visit(Guard n);

    R visit(If n);

    R visit(JmlAssert n);

    R visit(LabeledStatement n);

    R visit(LoopInit n);

    R visit(LoopScopeBlock n);

    R visit(MergePointStatement n);

    R visit(MethodBodyStatement n);

    R visit(MethodFrame n);

    R visit(Return n);

    R visit(SetStatement n);

    R visit(Switch n);

    R visit(SynchronizedBlock n);

    R visit(Throw n);

    R visit(TransactionStatement n);

    R visit(Try n);

    R visit(While n);

    R visit(ProgramElementName n);

    R visit(PermIndProgramElementName n);

    R visit(TempIndProgramElementName n);

    R visit(LocationVariable n);

    R visit(ProgramConstant n);

    R visit(ProgramMethod n);

    R visit(ProgramSV n);

    R visit(ReattachLoopInvariant n);

    R visit(SpecialConstructorCall n);

    R visit(StaticInitialisation n);

    R visit(SwitchToIf n);

    R visit(TypeOf n);

    R visit(Unpack n);

    R visit(UnwindLoop n);

    R visit(MultipleVarDecl n);

    R visit(PostWork n);

    R visit(IsStatic n);

    R visit(MethodCall n);

    R visit(ArrayLength n);

    R visit(ArrayPostDecl n);

    R visit(ConstructorCall n);

    R visit(CreateObject n);

    R visit(DoBreak n);

    R visit(EnhancedForElimination n);

    R visit(EvaluateArgs n);

    R visit(ExpandMethodBody n);

    R visit(ForInitUnfoldTransformer n);

    R visit(ForToWhile n);

    R visit(InitArrayCreation n);
}
