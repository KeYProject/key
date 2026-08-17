package org.key_project.java.ast.visitor;

import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;
import org.key_project.java.ast.*;

public interface VisitorWithDefaults<R> {

    default R visit(CompilationUnit n) {
        return defaultVisit(n);
    }

    default R visit(ContextStatementBlock n) {
        return defaultVisit(n);
    }

    default R visit(Import n) {
        return defaultVisit(n);
    }

    default R visit(StatementBlock n) {
        return defaultVisit(n);
    }

    default R visit(ArrayDeclaration n) {
        return defaultVisit(n);
    }

    default R visit(ClassDeclaration n) {
        return defaultVisit(n);
    }

    default R visit(ClassInitializer n) {
        return defaultVisit(n);
    }

    default R visit(ConstructorDeclaration n) {
        return defaultVisit(n);
    }

    default R visit(EnumClassDeclaration n) {
        return defaultVisit(n);
    }

    default R visit(Extends n) {
        return defaultVisit(n);
    }

    default R visit(FieldDeclaration n) {
        return defaultVisit(n);
    }

    default R visit(FieldSpecification n) {
        return defaultVisit(n);
    }

    default R visit(Implements n) {
        return defaultVisit(n);
    }

    default R visit(InterfaceDeclaration n) {
        return defaultVisit(n);
    }

    default R visit(LocalVariableDeclaration n) {
        return defaultVisit(n);
    }

    default R visit(MethodDeclaration n) {
        return defaultVisit(n);
    }

    default R visit(ParameterDeclaration n) {
        return defaultVisit(n);
    }

    default R visit(SuperArrayDeclaration n) {
        return defaultVisit(n);
    }

    default R visit(Throws n) {
        return defaultVisit(n);
    }

    default R visit(VariableSpecification n) {
        return defaultVisit(n);
    }

    default R visit(AnnotationUseSpecification n) {
        return defaultVisit(n);
    }

    default R visit(ArrayInitializer n) {
        return defaultVisit(n);
    }

    default R visit(ParenthesizedExpression n) {
        return defaultVisit(n);
    }

    default R visit(PassiveExpression n) {
        return defaultVisit(n);
    }

    default R visit(BooleanLiteral n) {
        return defaultVisit(n);
    }

    default R visit(DoubleLiteral n) {
        return defaultVisit(n);
    }

    default R visit(FloatLiteral n) {
        return defaultVisit(n);
    }

    default R visit(FreeLiteral n) {
        return defaultVisit(n);
    }

    default R visit(IntLiteral n) {
        return defaultVisit(n);
    }

    default R visit(LongLiteral n) {
        return defaultVisit(n);
    }

    default R visit(RealLiteral n) {
        return defaultVisit(n);
    }

    default R visit(StringLiteral n) {
        return defaultVisit(n);
    }

    default R visit(Assignment n) {
        return defaultVisit(n);
    }

    default R visit(BinaryOperator n) {
        return defaultVisit(n);
    }

    default R visit(UnaryOperator n) {
        return defaultVisit(n);
    }

    default R visit(LogicalFunctionOperator n) {
        return defaultVisit(n);
    }

    default R visit(Conditional n) {
        return defaultVisit(n);
    }

    default R visit(DLEmbeddedExpression n) {
        return defaultVisit(n);
    }

    default R visit(ExactInstanceof n) {
        return defaultVisit(n);
    }

    default R visit(Instanceof n) {
        return defaultVisit(n);
    }

    default R visit(New n) {
        return defaultVisit(n);
    }

    default R visit(NewArray n) {
        return defaultVisit(n);
    }

    default R visit(TypeCast n) {
        return defaultVisit(n);
    }

    default R visit(ArrayLengthReference n) {
        return defaultVisit(n);
    }

    default R visit(ArrayReference n) {
        return defaultVisit(n);
    }

    default R visit(ExecutionContext n) {
        return defaultVisit(n);
    }

    default R visit(FieldReference n) {
        return defaultVisit(n);
    }

    default R visit(MetaClassReference n) {
        return defaultVisit(n);
    }

    default R visit(MethodReference n) {
        return defaultVisit(n);
    }

    default R visit(PackageReference n) {
        return defaultVisit(n);
    }

    default R visit(SchemaTypeReference n) {
        return defaultVisit(n);
    }

    default R visit(SchematicFieldReference n) {
        return defaultVisit(n);
    }

    default R visit(SuperConstructorReference n) {
        return defaultVisit(n);
    }

    default R visit(SuperReference n) {
        return defaultVisit(n);
    }

    default R visit(ThisConstructorReference n) {
        return defaultVisit(n);
    }

    default R visit(ThisReference n) {
        return defaultVisit(n);
    }

    default R visit(TypeRef n) {
        return defaultVisit(n);
    }

    default R visit(VariableReference n) {
        return defaultVisit(n);
    }

    default R visit(Assert n) {
        return defaultVisit(n);
    }

    default R visit(Break n) {
        return defaultVisit(n);
    }

    default R visit(Case n) {
        return defaultVisit(n);
    }

    default R visit(Default n) {
        return defaultVisit(n);
    }

    default R visit(SingleCatch n) {
        return defaultVisit(n);
    }

    default R visit(CatchAllStatement n) {
        return defaultVisit(n);
    }

    default R visit(Ccatch n) {
        return defaultVisit(n);
    }

    default R visit(Continue n) {
        return defaultVisit(n);
    }

    default R visit(Do n) {
        return defaultVisit(n);
    }

    default R visit(EmptyStatement n) {
        return defaultVisit(n);
    }

    default R visit(EnhancedFor n) {
        return defaultVisit(n);
    }

    default R visit(Exec n) {
        return defaultVisit(n);
    }

    default R visit(For n) {
        return defaultVisit(n);
    }

    default R visit(ForUpdates n) {
        return defaultVisit(n);
    }

    default R visit(Guard n) {
        return defaultVisit(n);
    }

    default R visit(If n) {
        return defaultVisit(n);
    }

    default R visit(JmlAssert n) {
        return defaultVisit(n);
    }

    default R visit(LabeledStatement n) {
        return defaultVisit(n);
    }

    default R visit(LoopInit n) {
        return defaultVisit(n);
    }

    default R visit(LoopScopeBlock n) {
        return defaultVisit(n);
    }

    default R visit(MergePointStatement n) {
        return defaultVisit(n);
    }

    default R visit(MethodBodyStatement n) {
        return defaultVisit(n);
    }

    default R visit(MethodFrame n) {
        return defaultVisit(n);
    }

    default R visit(Return n) {
        return defaultVisit(n);
    }

    default R visit(SetStatement n) {
        return defaultVisit(n);
    }

    default R visit(Switch n) {
        return defaultVisit(n);
    }

    default R visit(SynchronizedBlock n) {
        return defaultVisit(n);
    }

    default R visit(Throw n) {
        return defaultVisit(n);
    }

    default R visit(TransactionStatement n) {
        return defaultVisit(n);
    }

    default R visit(Try n) {
        return defaultVisit(n);
    }

    default R visit(While n) {
        return defaultVisit(n);
    }

    default R visit(ProgramElementName n) {
        return defaultVisit(n);
    }

    default R visit(PermIndProgramElementName n) {
        return defaultVisit(n);
    }

    default R visit(TempIndProgramElementName n) {
        return defaultVisit(n);
    }

    default R visit(LocationVariable n) {
        return defaultVisit(n);
    }

    default R visit(ProgramConstant n) {
        return defaultVisit(n);
    }

    default R visit(ProgramMethod n) {
        return defaultVisit(n);
    }

    default R visit(ProgramSV n) {
        return defaultVisit(n);
    }

    default R visit(ReattachLoopInvariant n) {
        return defaultVisit(n);
    }

    default R visit(SpecialConstructorCall n) {
        return defaultVisit(n);
    }

    default R visit(StaticInitialisation n) {
        return defaultVisit(n);
    }

    default R visit(SwitchToIf n) {
        return defaultVisit(n);
    }

    default R visit(TypeOf n) {
        return defaultVisit(n);
    }

    default R visit(Unpack n) {
        return defaultVisit(n);
    }

    default R visit(UnwindLoop n) {
        return defaultVisit(n);
    }

    default R visit(MultipleVarDecl n) {
        return defaultVisit(n);
    }

    default R visit(PostWork n) {
        return defaultVisit(n);
    }

    default R visit(IsStatic n) {
        return defaultVisit(n);
    }

    default R visit(MethodCall n) {
        return defaultVisit(n);
    }

    default R visit(ArrayLength n) {
        return defaultVisit(n);
    }

    default R visit(ArrayPostDecl n) {
        return defaultVisit(n);
    }

    default R visit(ConstructorCall n) {
        return defaultVisit(n);
    }

    default R visit(CreateObject n) {
        return defaultVisit(n);
    }

    default R visit(DoBreak n) {
        return defaultVisit(n);
    }

    default R visit(EnhancedForElimination n) {
        return defaultVisit(n);
    }

    default R visit(EvaluateArgs n) {
        return defaultVisit(n);
    }

    default R visit(ExpandMethodBody n) {
        return defaultVisit(n);
    }

    default R visit(ForInitUnfoldTransformer n) {
        return defaultVisit(n);
    }

    default R visit(ForToWhile n) {
        return defaultVisit(n);
    }

    default R visit(InitArrayCreation n) {
        return defaultVisit(n);
    }

    R defaultVisit(JavaSourceElement n);
}
