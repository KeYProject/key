package org.key_project.java.ast.visitor;

import org.key_project.java.ast.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;

public interface VoidVisitor {

    void visit(CompilationUnit n);

    void visit(ContextStatementBlock n);

    void visit(Import n);

    void visit(StatementBlock n);

    void visit(ArrayDeclaration n);

    void visit(ClassDeclaration n);

    void visit(ClassInitializer n);

    void visit(ConstructorDeclaration n);

    void visit(EnumClassDeclaration n);

    void visit(Extends n);

    void visit(FieldDeclaration n);

    void visit(FieldSpecification n);

    void visit(Implements n);

    void visit(InterfaceDeclaration n);

    void visit(LocalVariableDeclaration n);

    void visit(MethodDeclaration n);

    void visit(ParameterDeclaration n);

    void visit(SuperArrayDeclaration n);

    void visit(Throws n);

    void visit(VariableSpecification n);

    void visit(AnnotationUseSpecification n);

    void visit(ArrayInitializer n);

    void visit(ParenthesizedExpression n);

    void visit(PassiveExpression n);

    void visit(BooleanLiteral n);

    void visit(DoubleLiteral n);

    void visit(FloatLiteral n);

    void visit(FreeLiteral n);

    void visit(IntLiteral n);

    void visit(LongLiteral n);

    void visit(RealLiteral n);

    void visit(StringLiteral n);

    void visit(Assignment n);

    void visit(BinaryOperator n);

    void visit(UnaryOperator n);

    void visit(LogicalFunctionOperator n);

    void visit(Conditional n);

    void visit(DLEmbeddedExpression n);

    void visit(ExactInstanceof n);

    void visit(Instanceof n);

    void visit(New n);

    void visit(NewArray n);

    void visit(TypeCast n);

    void visit(ArrayLengthReference n);

    void visit(ArrayReference n);

    void visit(ExecutionContext n);

    void visit(FieldReference n);

    void visit(MetaClassReference n);

    void visit(MethodReference n);

    void visit(PackageReference n);

    void visit(SchemaTypeReference n);

    void visit(SchematicFieldReference n);

    void visit(SuperConstructorReference n);

    void visit(SuperReference n);

    void visit(ThisConstructorReference n);

    void visit(ThisReference n);

    void visit(TypeRef n);

    void visit(VariableReference n);

    void visit(Assert n);

    void visit(Break n);

    void visit(Case n);

    void visit(Default n);

    void visit(SingleCatch n);

    void visit(CatchAllStatement n);

    void visit(Ccatch n);

    void visit(Continue n);

    void visit(Do n);

    void visit(EmptyStatement n);

    void visit(EnhancedFor n);

    void visit(Exec n);

    void visit(For n);

    void visit(ForUpdates n);

    void visit(Guard n);

    void visit(If n);

    void visit(JmlAssert n);

    void visit(LabeledStatement n);

    void visit(LoopInit n);

    void visit(LoopScopeBlock n);

    void visit(MergePointStatement n);

    void visit(MethodBodyStatement n);

    void visit(MethodFrame n);

    void visit(Return n);

    void visit(SetStatement n);

    void visit(Switch n);

    void visit(SynchronizedBlock n);

    void visit(Throw n);

    void visit(TransactionStatement n);

    void visit(Try n);

    void visit(While n);

    void visit(ProgramElementName n);

    void visit(PermIndProgramElementName n);

    void visit(TempIndProgramElementName n);

    void visit(LocationVariable n);

    void visit(ProgramConstant n);

    void visit(ProgramMethod n);

    void visit(ProgramSV n);

    void visit(ReattachLoopInvariant n);

    void visit(SpecialConstructorCall n);

    void visit(StaticInitialisation n);

    void visit(SwitchToIf n);

    void visit(TypeOf n);

    void visit(Unpack n);

    void visit(UnwindLoop n);

    void visit(MultipleVarDecl n);

    void visit(PostWork n);

    void visit(IsStatic n);

    void visit(MethodCall n);

    void visit(ArrayLength n);

    void visit(ArrayPostDecl n);

    void visit(ConstructorCall n);

    void visit(CreateObject n);

    void visit(DoBreak n);

    void visit(EnhancedForElimination n);

    void visit(EvaluateArgs n);

    void visit(ExpandMethodBody n);

    void visit(ForInitUnfoldTransformer n);

    void visit(ForToWhile n);

    void visit(InitArrayCreation n);
}
