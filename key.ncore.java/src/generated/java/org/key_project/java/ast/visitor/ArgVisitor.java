package org.key_project.java.ast.visitor;

import org.key_project.java.ast.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;

public interface ArgVisitor<R, A> {

    R visit(CompilationUnit n, A arg);

    R visit(ContextStatementBlock n, A arg);

    R visit(Import n, A arg);

    R visit(StatementBlock n, A arg);

    R visit(ArrayDeclaration n, A arg);

    R visit(ClassDeclaration n, A arg);

    R visit(ClassInitializer n, A arg);

    R visit(ConstructorDeclaration n, A arg);

    R visit(EnumClassDeclaration n, A arg);

    R visit(Extends n, A arg);

    R visit(FieldDeclaration n, A arg);

    R visit(FieldSpecification n, A arg);

    R visit(Implements n, A arg);

    R visit(InterfaceDeclaration n, A arg);

    R visit(LocalVariableDeclaration n, A arg);

    R visit(MethodDeclaration n, A arg);

    R visit(ParameterDeclaration n, A arg);

    R visit(SuperArrayDeclaration n, A arg);

    R visit(Throws n, A arg);

    R visit(VariableSpecification n, A arg);

    R visit(AnnotationUseSpecification n, A arg);

    R visit(ArrayInitializer n, A arg);

    R visit(ParenthesizedExpression n, A arg);

    R visit(PassiveExpression n, A arg);

    R visit(BooleanLiteral n, A arg);

    R visit(DoubleLiteral n, A arg);

    R visit(FloatLiteral n, A arg);

    R visit(FreeLiteral n, A arg);

    R visit(IntLiteral n, A arg);

    R visit(LongLiteral n, A arg);

    R visit(RealLiteral n, A arg);

    R visit(StringLiteral n, A arg);

    R visit(Assignment n, A arg);

    R visit(BinaryOperator n, A arg);

    R visit(UnaryOperator n, A arg);

    R visit(LogicalFunctionOperator n, A arg);

    R visit(Conditional n, A arg);

    R visit(DLEmbeddedExpression n, A arg);

    R visit(ExactInstanceof n, A arg);

    R visit(Instanceof n, A arg);

    R visit(New n, A arg);

    R visit(NewArray n, A arg);

    R visit(TypeCast n, A arg);

    R visit(ArrayLengthReference n, A arg);

    R visit(ArrayReference n, A arg);

    R visit(ExecutionContext n, A arg);

    R visit(FieldReference n, A arg);

    R visit(MetaClassReference n, A arg);

    R visit(MethodReference n, A arg);

    R visit(PackageReference n, A arg);

    R visit(SchemaTypeReference n, A arg);

    R visit(SchematicFieldReference n, A arg);

    R visit(SuperConstructorReference n, A arg);

    R visit(SuperReference n, A arg);

    R visit(ThisConstructorReference n, A arg);

    R visit(ThisReference n, A arg);

    R visit(TypeRef n, A arg);

    R visit(VariableReference n, A arg);

    R visit(Assert n, A arg);

    R visit(Break n, A arg);

    R visit(Case n, A arg);

    R visit(Default n, A arg);

    R visit(SingleCatch n, A arg);

    R visit(CatchAllStatement n, A arg);

    R visit(Ccatch n, A arg);

    R visit(Continue n, A arg);

    R visit(Do n, A arg);

    R visit(EmptyStatement n, A arg);

    R visit(EnhancedFor n, A arg);

    R visit(Exec n, A arg);

    R visit(For n, A arg);

    R visit(ForUpdates n, A arg);

    R visit(Guard n, A arg);

    R visit(If n, A arg);

    R visit(JmlAssert n, A arg);

    R visit(LabeledStatement n, A arg);

    R visit(LoopInit n, A arg);

    R visit(LoopScopeBlock n, A arg);

    R visit(MergePointStatement n, A arg);

    R visit(MethodBodyStatement n, A arg);

    R visit(MethodFrame n, A arg);

    R visit(Return n, A arg);

    R visit(SetStatement n, A arg);

    R visit(Switch n, A arg);

    R visit(SynchronizedBlock n, A arg);

    R visit(Throw n, A arg);

    R visit(TransactionStatement n, A arg);

    R visit(Try n, A arg);

    R visit(While n, A arg);

    R visit(ProgramElementName n, A arg);

    R visit(PermIndProgramElementName n, A arg);

    R visit(TempIndProgramElementName n, A arg);

    R visit(LocationVariable n, A arg);

    R visit(ProgramConstant n, A arg);

    R visit(ProgramMethod n, A arg);

    R visit(ProgramSV n, A arg);

    R visit(ReattachLoopInvariant n, A arg);

    R visit(SpecialConstructorCall n, A arg);

    R visit(StaticInitialisation n, A arg);

    R visit(SwitchToIf n, A arg);

    R visit(TypeOf n, A arg);

    R visit(Unpack n, A arg);

    R visit(UnwindLoop n, A arg);

    R visit(MultipleVarDecl n, A arg);

    R visit(PostWork n, A arg);

    R visit(IsStatic n, A arg);

    R visit(MethodCall n, A arg);

    R visit(ArrayLength n, A arg);

    R visit(ArrayPostDecl n, A arg);

    R visit(ConstructorCall n, A arg);

    R visit(CreateObject n, A arg);

    R visit(DoBreak n, A arg);

    R visit(EnhancedForElimination n, A arg);

    R visit(EvaluateArgs n, A arg);

    R visit(ExpandMethodBody n, A arg);

    R visit(ForInitUnfoldTransformer n, A arg);

    R visit(ForToWhile n, A arg);

    R visit(InitArrayCreation n, A arg);
}
