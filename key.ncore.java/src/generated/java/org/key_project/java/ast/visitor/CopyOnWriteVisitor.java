package org.key_project.java.ast.visitor;

import org.key_project.java.ast.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;

public class CopyOnWriteVisitor implements Visitor<JavaSourceElement> {

    protected <T extends Visitable> T accept(T n) {
        return n != null ? n.accept(this) : null;
    }

    protected <T extends Visitable> ImmutableList<T> accept(ImmutableList<T> n) {
        return n != null ? n.stream().map(it -> (T) it.accept(this)).collect(RoList.collector()) : null;
    }

    protected <T> T accept(T n) {
        return n;
    }

    @Override()
    public org.key_project.java.ast.CompilationUnit visit(CompilationUnit n) {
        var b = n.builder();
        b.packageReference = (PackageReference) accept(n.packageReference());
        b.imports = (ImmutableList<Import>) accept(n.imports());
        b.typeDeclarations = (ImmutableList<TypeDeclaration>) accept(n.typeDeclarations());
        boolean clean = (n.packageReference() == b.packageReference) && (n.imports() == b.imports) && (n.typeDeclarations() == b.typeDeclarations) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ContextStatementBlock visit(ContextStatementBlock n) {
        var b = n.builder();
        b.executionContext = (IExecutionContext) accept(n.executionContext());
        b.innerMostMethodFrame = (MethodFrame) accept(n.innerMostMethodFrame());
        b.statement = (ImmutableList<Statement>) accept(n.statement());
        boolean clean = (n.executionContext() == b.executionContext) && (n.innerMostMethodFrame() == b.innerMostMethodFrame) && (n.positionInfo() == b.positionInfo) && (n.statement() == b.statement) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Import visit(Import n) {
        var b = n.builder();
        b.reference = (TypeReferenceInfix) accept(n.reference());
        boolean clean = (n.isMultiImport() == b.isMultiImport) && (n.isStatic() == b.isStatic) && (n.reference() == b.reference) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.StatementBlock visit(StatementBlock n) {
        var b = n.builder();
        b.statement = (ImmutableList<Statement>) accept(n.statement());
        b.innerMostMethodFrame = (MethodFrame) accept(n.innerMostMethodFrame());
        boolean clean = (n.statement() == b.statement) && (n.innerMostMethodFrame() == b.innerMostMethodFrame) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ArrayDeclaration visit(ArrayDeclaration n) {
        var b = n.builder();
        b.fullName = (ProgramElementName) accept(n.fullName());
        b.members = (ImmutableList<MemberDeclaration>) accept(n.members());
        b.name = (ProgramElementName) accept(n.name());
        boolean clean = (n.fullName() == b.fullName) && (n.isLibrary() == b.isLibrary) && (n.jmlModifiers() == b.jmlModifiers) && (n.members() == b.members) && (n.name() == b.name) && (n.parentIsInterfaceDeclaration() == b.parentIsInterfaceDeclaration) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ClassDeclaration visit(ClassDeclaration n) {
        var b = n.builder();
        b.extending = (Extends) accept(n.extending());
        b.implementing = (Implements) accept(n.implementing());
        b.fullName = (ProgramElementName) accept(n.fullName());
        b.members = (ImmutableList<MemberDeclaration>) accept(n.members());
        b.name = (ProgramElementName) accept(n.name());
        boolean clean = (n.extending() == b.extending) && (n.implementing() == b.implementing) && (n.isInnerClass() == b.isInnerClass) && (n.isLocalClass() == b.isLocalClass) && (n.isAnonymousClass() == b.isAnonymousClass) && (n.fullName() == b.fullName) && (n.isLibrary() == b.isLibrary) && (n.jmlModifiers() == b.jmlModifiers) && (n.members() == b.members) && (n.name() == b.name) && (n.parentIsInterfaceDeclaration() == b.parentIsInterfaceDeclaration) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ClassInitializer visit(ClassInitializer n) {
        var b = n.builder();
        b.body = (StatementBlock) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ConstructorDeclaration visit(ConstructorDeclaration n) {
        var b = n.builder();
        b.body = (StatementBlock) accept(n.body());
        b.exceptions = (Throws) accept(n.exceptions());
        b.name = (ProgramElementName) accept(n.name());
        b.parameters = (ImmutableList<ParameterDeclaration>) accept(n.parameters());
        b.returnType = (TypeReference) accept(n.returnType());
        boolean clean = (n.body() == b.body) && (n.exceptions() == b.exceptions) && (n.jmlModifiers() == b.jmlModifiers) && (n.name() == b.name) && (n.parameters() == b.parameters) && (n.parentIsInterfaceDeclaration() == b.parentIsInterfaceDeclaration) && (n.positionInfo() == b.positionInfo) && (n.returnType() == b.returnType) && (n.voidComments() == b.voidComments) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.EnumClassDeclaration visit(EnumClassDeclaration n) {
        var b = n.builder();
        b.extending = (Extends) accept(n.extending());
        b.fullName = (ProgramElementName) accept(n.fullName());
        b.implementing = (Implements) accept(n.implementing());
        b.members = (ImmutableList<MemberDeclaration>) accept(n.members());
        b.name = (ProgramElementName) accept(n.name());
        boolean clean = (n.extending() == b.extending) && (n.fullName() == b.fullName) && (n.implementing() == b.implementing) && (n.isAnonymousClass() == b.isAnonymousClass) && (n.isInnerClass() == b.isInnerClass) && (n.isLibrary() == b.isLibrary) && (n.isLocalClass() == b.isLocalClass) && (n.jmlModifiers() == b.jmlModifiers) && (n.members() == b.members) && (n.name() == b.name) && (n.parentIsInterfaceDeclaration() == b.parentIsInterfaceDeclaration) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Extends visit(Extends n) {
        var b = n.builder();
        b.supertypes = (ImmutableList<TypeReference>) accept(n.supertypes());
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.supertypes() == b.supertypes) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.FieldDeclaration visit(FieldDeclaration n) {
        var b = n.builder();
        b.fieldSpecs = (ImmutableList<FieldSpecification>) accept(n.fieldSpecs());
        b.typeReference = (TypeReference) accept(n.typeReference());
        boolean clean = (n.fieldSpecs() == b.fieldSpecs) && (n.parentIsInterfaceDeclaration() == b.parentIsInterfaceDeclaration) && (n.positionInfo() == b.positionInfo) && (n.typeReference() == b.typeReference) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.FieldSpecification visit(FieldSpecification n) {
        var b = n.builder();
        b.type = (Type) accept(n.type());
        b.var = (ProgramVariable) accept(n.var());
        b.init = (Expression) accept(n.init());
        b.initializer = (Expression) accept(n.initializer());
        b.programVariable = (IProgramVariable) accept(n.programVariable());
        boolean clean = (n.type() == b.type) && (n.dimensions() == b.dimensions) && (n.var() == b.var) && (n.init() == b.init) && (n.initializer() == b.initializer) && (n.positionInfo() == b.positionInfo) && (n.programVariable() == b.programVariable) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Implements visit(Implements n) {
        var b = n.builder();
        b.typeRefs = (ImmutableList<TypeReference>) accept(n.typeRefs());
        b.supertypes = (ImmutableList<TypeReference>) accept(n.supertypes());
        boolean clean = (n.typeRefs() == b.typeRefs) && (n.positionInfo() == b.positionInfo) && (n.supertypes() == b.supertypes) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.InterfaceDeclaration visit(InterfaceDeclaration n) {
        var b = n.builder();
        b.extending = (ImmutableList<TypeReference>) accept(n.extending());
        b.fullName = (ProgramElementName) accept(n.fullName());
        b.members = (ImmutableList<MemberDeclaration>) accept(n.members());
        b.name = (ProgramElementName) accept(n.name());
        boolean clean = (n.extending() == b.extending) && (n.fullName() == b.fullName) && (n.isLibrary() == b.isLibrary) && (n.jmlModifiers() == b.jmlModifiers) && (n.members() == b.members) && (n.name() == b.name) && (n.parentIsInterfaceDeclaration() == b.parentIsInterfaceDeclaration) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.LocalVariableDeclaration visit(LocalVariableDeclaration n) {
        var b = n.builder();
        b.varSpecs = (ImmutableList<VariableSpecification>) accept(n.varSpecs());
        b.typeReference = (TypeReference) accept(n.typeReference());
        boolean clean = (n.varSpecs() == b.varSpecs) && (n.parentIsInterfaceDeclaration() == b.parentIsInterfaceDeclaration) && (n.positionInfo() == b.positionInfo) && (n.typeReference() == b.typeReference) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.MethodDeclaration visit(MethodDeclaration n) {
        var b = n.builder();
        b.returnType = (TypeReference) accept(n.returnType());
        b.name = (ProgramElementName) accept(n.name());
        b.parameters = (ImmutableList<ParameterDeclaration>) accept(n.parameters());
        b.exceptions = (Throws) accept(n.exceptions());
        b.body = (StatementBlock) accept(n.body());
        boolean clean = (n.returnType() == b.returnType) && (n.voidComments() == b.voidComments) && (n.name() == b.name) && (n.parameters() == b.parameters) && (n.exceptions() == b.exceptions) && (n.body() == b.body) && (n.jmlModifiers() == b.jmlModifiers) && (n.parentIsInterfaceDeclaration() == b.parentIsInterfaceDeclaration) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ParameterDeclaration visit(ParameterDeclaration n) {
        var b = n.builder();
        b.varSpec = (ImmutableList<VariableSpecification>) accept(n.varSpec());
        b.typeReference = (TypeReference) accept(n.typeReference());
        boolean clean = (n.varSpec() == b.varSpec) && (n.parentIsInterfaceDeclaration() == b.parentIsInterfaceDeclaration) && (n.positionInfo() == b.positionInfo) && (n.typeReference() == b.typeReference) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.SuperArrayDeclaration visit(SuperArrayDeclaration n) {
        var b = n.builder();
        b.name = (ProgramElementName) accept(n.name());
        b.length = (FieldDeclaration) accept(n.length());
        b.fullName = (ProgramElementName) accept(n.fullName());
        b.members = (ImmutableList<MemberDeclaration>) accept(n.members());
        boolean clean = (n.name() == b.name) && (n.length() == b.length) && (n.fullName() == b.fullName) && (n.isLibrary() == b.isLibrary) && (n.jmlModifiers() == b.jmlModifiers) && (n.members() == b.members) && (n.parentIsInterfaceDeclaration() == b.parentIsInterfaceDeclaration) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Throws visit(Throws n) {
        var b = n.builder();
        b.exceptions = (ImmutableList<TypeReference>) accept(n.exceptions());
        boolean clean = (n.exceptions() == b.exceptions) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.VariableSpecification visit(VariableSpecification n) {
        var b = n.builder();
        b.initializer = (Expression) accept(n.initializer());
        b.type = (Type) accept(n.type());
        b.programVariable = (IProgramVariable) accept(n.programVariable());
        boolean clean = (n.initializer() == b.initializer) && (n.dimensions() == b.dimensions) && (n.type() == b.type) && (n.programVariable() == b.programVariable) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.AnnotationUseSpecification visit(AnnotationUseSpecification n) {
        var b = n.builder();
        b.tr = (TypeReference) accept(n.tr());
        boolean clean = (n.tr() == b.tr) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ArrayInitializer visit(ArrayInitializer n) {
        var b = n.builder();
        b.kjt = (KeYJavaType) accept(n.kjt());
        boolean clean = (n.kjt() == b.kjt) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ParenthesizedExpression visit(ParenthesizedExpression n) {
        var b = n.builder();
        b.child = (Expression) accept(n.child());
        boolean clean = (n.child() == b.child) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.PassiveExpression visit(PassiveExpression n) {
        var b = n.builder();
        b.child = (Expression) accept(n.child());
        boolean clean = (n.child() == b.child) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.BooleanLiteral visit(BooleanLiteral n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.value() == b.value) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.DoubleLiteral visit(DoubleLiteral n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.value() == b.value) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.FloatLiteral visit(FloatLiteral n) {
        var b = n.builder();
        boolean clean = (n.value() == b.value) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.FreeLiteral visit(FreeLiteral n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.value() == b.value) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.IntLiteral visit(IntLiteral n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.LongLiteral visit(LongLiteral n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.RealLiteral visit(RealLiteral n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.value() == b.value) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.StringLiteral visit(StringLiteral n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.value() == b.value) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Assignment visit(Assignment n) {
        var b = n.builder();
        b.left = (Expression) accept(n.left());
        b.right = (Expression) accept(n.right());
        boolean clean = (n.kind() == b.kind) && (n.left() == b.left) && (n.right() == b.right) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.BinaryOperator visit(BinaryOperator n) {
        var b = n.builder();
        b.left = (Expression) accept(n.left());
        b.right = (Expression) accept(n.right());
        boolean clean = (n.kind() == b.kind) && (n.left() == b.left) && (n.right() == b.right) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.UnaryOperator visit(UnaryOperator n) {
        var b = n.builder();
        b.child = (Expression) accept(n.child());
        boolean clean = (n.kind() == b.kind) && (n.child() == b.child) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.LogicalFunctionOperator visit(LogicalFunctionOperator n) {
        var b = n.builder();
        b.function = (LogicFunction) accept(n.function());
        b.arguments = (ImmutableList<Expression>) accept(n.arguments());
        boolean clean = (n.function() == b.function) && (n.arguments() == b.arguments) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Conditional visit(Conditional n) {
        var b = n.builder();
        b.condition = (Expression) accept(n.condition());
        b.thenExpr = (Expression) accept(n.thenExpr());
        b.elseExpr = (Expression) accept(n.elseExpr());
        boolean clean = (n.condition() == b.condition) && (n.thenExpr() == b.thenExpr) && (n.elseExpr() == b.elseExpr) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.DLEmbeddedExpression visit(DLEmbeddedExpression n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ExactInstanceof visit(ExactInstanceof n) {
        var b = n.builder();
        b.typeReference = (TypeReference) accept(n.typeReference());
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.typeReference() == b.typeReference) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Instanceof visit(Instanceof n) {
        var b = n.builder();
        b.typeReference = (TypeReference) accept(n.typeReference());
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.typeReference() == b.typeReference) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.New visit(New n) {
        var b = n.builder();
        b.anonymousClass = (ClassDeclaration) accept(n.anonymousClass());
        b.accessPath = (ReferencePrefix) accept(n.accessPath());
        b.typeReference = (TypeReference) accept(n.typeReference());
        boolean clean = (n.anonymousClass() == b.anonymousClass) && (n.accessPath() == b.accessPath) && (n.positionInfo() == b.positionInfo) && (n.typeReference() == b.typeReference) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.NewArray visit(NewArray n) {
        var b = n.builder();
        b.arrayInitializer = (ArrayInitializer) accept(n.arrayInitializer());
        b.typeReference = (TypeReference) accept(n.typeReference());
        boolean clean = (n.dimensions() == b.dimensions) && (n.arrayInitializer() == b.arrayInitializer) && (n.positionInfo() == b.positionInfo) && (n.typeReference() == b.typeReference) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.TypeCast visit(TypeCast n) {
        var b = n.builder();
        b.typeReference = (TypeReference) accept(n.typeReference());
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.typeReference() == b.typeReference) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ArrayLengthReference visit(ArrayLengthReference n) {
        var b = n.builder();
        b.prefix = (ReferencePrefix) accept(n.prefix());
        boolean clean = (n.prefix() == b.prefix) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ArrayReference visit(ArrayReference n) {
        var b = n.builder();
        b.prefix = (ReferencePrefix) accept(n.prefix());
        b.inits = (ImmutableList<Expression>) accept(n.inits());
        boolean clean = (n.prefix() == b.prefix) && (n.inits() == b.inits) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ExecutionContext visit(ExecutionContext n) {
        var b = n.builder();
        b.classContext = (TypeReference) accept(n.classContext());
        b.runtimeInstance = (ReferencePrefix) accept(n.runtimeInstance());
        boolean clean = (n.classContext() == b.classContext) && (n.runtimeInstance() == b.runtimeInstance) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.FieldReference visit(FieldReference n) {
        var b = n.builder();
        b.prefix = (ReferencePrefix) accept(n.prefix());
        b.variable = (ProgramVariable) accept(n.variable());
        boolean clean = (n.prefix() == b.prefix) && (n.positionInfo() == b.positionInfo) && (n.variable() == b.variable) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.MetaClassReference visit(MetaClassReference n) {
        var b = n.builder();
        b.typeReference = (TypeReference) accept(n.typeReference());
        boolean clean = (n.typeReference() == b.typeReference) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.MethodReference visit(MethodReference n) {
        var b = n.builder();
        b.prefix = (ReferencePrefix) accept(n.prefix());
        b.name = (MethodName) accept(n.name());
        boolean clean = (n.prefix() == b.prefix) && (n.name() == b.name) && (n.arguments() == b.arguments) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.PackageReference visit(PackageReference n) {
        var b = n.builder();
        b.prefix = (ReferencePrefix) accept(n.prefix());
        b.name = (ProgramElementName) accept(n.name());
        boolean clean = (n.prefix() == b.prefix) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.SchemaTypeReference visit(SchemaTypeReference n) {
        var b = n.builder();
        b.name = (ProgramElementName) accept(n.name());
        b.prefix = (ReferencePrefix) accept(n.prefix());
        boolean clean = (n.dimensions() == b.dimensions) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.prefix() == b.prefix) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.SchematicFieldReference visit(SchematicFieldReference n) {
        var b = n.builder();
        b.schemaVariable = (SchemaVariable) accept(n.schemaVariable());
        b.prefix = (ReferencePrefix) accept(n.prefix());
        b.variable = (ProgramVariable) accept(n.variable());
        boolean clean = (n.schemaVariable() == b.schemaVariable) && (n.positionInfo() == b.positionInfo) && (n.prefix() == b.prefix) && (n.variable() == b.variable) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.SuperConstructorReference visit(SuperConstructorReference n) {
        var b = n.builder();
        b.prefix = (ReferencePrefix) accept(n.prefix());
        b.arguments = (ImmutableList<Expression>) accept(n.arguments());
        boolean clean = (n.prefix() == b.prefix) && (n.arguments() == b.arguments) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.SuperReference visit(SuperReference n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ThisConstructorReference visit(ThisConstructorReference n) {
        var b = n.builder();
        b.arguments = (ImmutableList<Expression>) accept(n.arguments());
        boolean clean = (n.arguments() == b.arguments) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ThisReference visit(ThisReference n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.TypeRef visit(TypeRef n) {
        var b = n.builder();
        b.name = (ProgramElementName) accept(n.name());
        b.prefix = (ReferencePrefix) accept(n.prefix());
        boolean clean = (n.dimensions() == b.dimensions) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.prefix() == b.prefix) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.VariableReference visit(VariableReference n) {
        var b = n.builder();
        b.variable = (ProgramVariable) accept(n.variable());
        boolean clean = (n.variable() == b.variable) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Assert visit(Assert n) {
        var b = n.builder();
        b.expression = (Expression) accept(n.expression());
        boolean clean = (n.expression() == b.expression) && (n.message() == b.message) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Break visit(Break n) {
        var b = n.builder();
        b.name = (Label) accept(n.name());
        boolean clean = (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Case visit(Case n) {
        var b = n.builder();
        b.expression = (Expression) accept(n.expression());
        b.body = (ImmutableList<Statement>) accept(n.body());
        boolean clean = (n.expression() == b.expression) && (n.body() == b.body) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Default visit(Default n) {
        var b = n.builder();
        b.body = (ImmutableList<Statement>) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.SingleCatch visit(SingleCatch n) {
        var b = n.builder();
        b.parameter = (ParameterDeclaration) accept(n.parameter());
        b.body = (StatementBlock) accept(n.body());
        boolean clean = (n.parameter() == b.parameter) && (n.body() == b.body) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.CatchAllStatement visit(CatchAllStatement n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Ccatch visit(Ccatch n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Continue visit(Continue n) {
        var b = n.builder();
        b.name = (Label) accept(n.name());
        boolean clean = (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Do visit(Do n) {
        var b = n.builder();
        b.attachedJml = (ImmutableList<TextualJMLConstruct>) accept(n.attachedJml());
        b.body = (Statement) accept(n.body());
        b.guard = (IGuard) accept(n.guard());
        b.inits = (ILoopInit) accept(n.inits());
        b.updates = (IForUpdates) accept(n.updates());
        boolean clean = (n.attachedJml() == b.attachedJml) && (n.body() == b.body) && (n.guard() == b.guard) && (n.inits() == b.inits) && (n.positionInfo() == b.positionInfo) && (n.updates() == b.updates) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.EmptyStatement visit(EmptyStatement n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.EnhancedFor visit(EnhancedFor n) {
        var b = n.builder();
        b.attachedJml = (ImmutableList<TextualJMLConstruct>) accept(n.attachedJml());
        b.body = (Statement) accept(n.body());
        b.guard = (IGuard) accept(n.guard());
        b.inits = (ILoopInit) accept(n.inits());
        b.updates = (IForUpdates) accept(n.updates());
        boolean clean = (n.attachedJml() == b.attachedJml) && (n.body() == b.body) && (n.guard() == b.guard) && (n.inits() == b.inits) && (n.positionInfo() == b.positionInfo) && (n.updates() == b.updates) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Exec visit(Exec n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.For visit(For n) {
        var b = n.builder();
        b.attachedJml = (ImmutableList<TextualJMLConstruct>) accept(n.attachedJml());
        b.body = (Statement) accept(n.body());
        b.guard = (IGuard) accept(n.guard());
        b.inits = (ILoopInit) accept(n.inits());
        b.updates = (IForUpdates) accept(n.updates());
        boolean clean = (n.attachedJml() == b.attachedJml) && (n.body() == b.body) && (n.guard() == b.guard) && (n.inits() == b.inits) && (n.positionInfo() == b.positionInfo) && (n.updates() == b.updates) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ForUpdates visit(ForUpdates n) {
        var b = n.builder();
        b.updates = (ImmutableList<Expression>) accept(n.updates());
        boolean clean = (n.updates() == b.updates) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Guard visit(Guard n) {
        var b = n.builder();
        b.expr = (Expression) accept(n.expr());
        boolean clean = (n.expr() == b.expr) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.If visit(If n) {
        var b = n.builder();
        b.condition = (Expression) accept(n.condition());
        b.thenBranch = (Statement) accept(n.thenBranch());
        b.elseBranch = (Statement) accept(n.elseBranch());
        boolean clean = (n.condition() == b.condition) && (n.thenBranch() == b.thenBranch) && (n.elseBranch() == b.elseBranch) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.JmlAssert visit(JmlAssert n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.LabeledStatement visit(LabeledStatement n) {
        var b = n.builder();
        b.name = (Label) accept(n.name());
        b.body = (Statement) accept(n.body());
        boolean clean = (n.name() == b.name) && (n.body() == b.body) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.LoopInit visit(LoopInit n) {
        var b = n.builder();
        b.inits = (ImmutableList<LoopInitializer>) accept(n.inits());
        boolean clean = (n.inits() == b.inits) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.LoopScopeBlock visit(LoopScopeBlock n) {
        var b = n.builder();
        b.variant = (Expression) accept(n.variant());
        b.body = (Statement) accept(n.body());
        boolean clean = (n.variant() == b.variant) && (n.body() == b.body) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.MergePointStatement visit(MergePointStatement n) {
        var b = n.builder();
        b.identifier = (IProgramVariable) accept(n.identifier());
        boolean clean = (n.identifier() == b.identifier) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.MethodBodyStatement visit(MethodBodyStatement n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.MethodFrame visit(MethodFrame n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Return visit(Return n) {
        var b = n.builder();
        b.expression = (Expression) accept(n.expression());
        boolean clean = (n.expression() == b.expression) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.SetStatement visit(SetStatement n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Switch visit(Switch n) {
        var b = n.builder();
        b.expression = (Expression) accept(n.expression());
        b.branches = (ImmutableList<Branch>) accept(n.branches());
        boolean clean = (n.expression() == b.expression) && (n.branches() == b.branches) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.SynchronizedBlock visit(SynchronizedBlock n) {
        var b = n.builder();
        b.expression = (Expression) accept(n.expression());
        b.body = (StatementBlock) accept(n.body());
        boolean clean = (n.expression() == b.expression) && (n.body() == b.body) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Throw visit(Throw n) {
        var b = n.builder();
        b.expression = (Expression) accept(n.expression());
        boolean clean = (n.expression() == b.expression) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.TransactionStatement visit(TransactionStatement n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Try visit(Try n) {
        var b = n.builder();
        b.tryBlock = (StatementBlock) accept(n.tryBlock());
        b.catches = (ImmutableList<Catch>) accept(n.catches());
        b.finallyBlock = (StatementBlock) accept(n.finallyBlock());
        boolean clean = (n.tryBlock() == b.tryBlock) && (n.catches() == b.catches) && (n.finallyBlock() == b.finallyBlock) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.While visit(While n) {
        var b = n.builder();
        b.attachedJml = (ImmutableList<TextualJMLConstruct>) accept(n.attachedJml());
        b.body = (Statement) accept(n.body());
        b.guard = (IGuard) accept(n.guard());
        b.inits = (ILoopInit) accept(n.inits());
        b.updates = (IForUpdates) accept(n.updates());
        boolean clean = (n.attachedJml() == b.attachedJml) && (n.body() == b.body) && (n.guard() == b.guard) && (n.inits() == b.inits) && (n.positionInfo() == b.positionInfo) && (n.updates() == b.updates) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ProgramElementName visit(ProgramElementName n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.PermIndProgramElementName visit(PermIndProgramElementName n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.TempIndProgramElementName visit(TempIndProgramElementName n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.LocationVariable visit(LocationVariable n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ProgramConstant visit(ProgramConstant n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ProgramMethod visit(ProgramMethod n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ProgramSV visit(ProgramSV n) {
        var b = n.builder();
        boolean clean = (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ReattachLoopInvariant visit(ReattachLoopInvariant n) {
        var b = n.builder();
        b.body = (LoopStatment) accept(n.body());
        boolean clean = (n.name() == b.name) && (n.body() == b.body) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.SpecialConstructorCall visit(SpecialConstructorCall n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.name() == b.name) && (n.body() == b.body) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.StaticInitialisation visit(StaticInitialisation n) {
        var b = n.builder();
        b.body = (Expression) accept(n.body());
        boolean clean = (n.name() == b.name) && (n.body() == b.body) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.SwitchToIf visit(SwitchToIf n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.TypeOf visit(TypeOf n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.Unpack visit(Unpack n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.UnwindLoop visit(UnwindLoop n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.MultipleVarDecl visit(MultipleVarDecl n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.PostWork visit(PostWork n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.IsStatic visit(IsStatic n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.MethodCall visit(MethodCall n) {
        var b = n.builder();
        b.methRef = (MethodReference) accept(n.methRef());
        b.newContext = (ReferencePrefix) accept(n.newContext());
        b.pvar = (ProgramVariable) accept(n.pvar());
        b.arguments = (ImmutableList<Expression>) accept(n.arguments());
        b.staticPrefixType = (KeYJavaType) accept(n.staticPrefixType());
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.methRef() == b.methRef) && (n.newContext() == b.newContext) && (n.pvar() == b.pvar) && (n.arguments() == b.arguments) && (n.staticPrefixType() == b.staticPrefixType) && (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ArrayLength visit(ArrayLength n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ArrayPostDecl visit(ArrayPostDecl n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ConstructorCall visit(ConstructorCall n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.CreateObject visit(CreateObject n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.DoBreak visit(DoBreak n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.EnhancedForElimination visit(EnhancedForElimination n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.EvaluateArgs visit(EvaluateArgs n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ExpandMethodBody visit(ExpandMethodBody n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ForInitUnfoldTransformer visit(ForInitUnfoldTransformer n) {
        var b = n.builder();
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.ForToWhile visit(ForToWhile n) {
        var b = n.builder();
        b.innerLabel = (SchemaVariable) accept(n.innerLabel());
        b.outerLabel = (SchemaVariable) accept(n.outerLabel());
        b.body = (Statement) accept(n.body());
        boolean clean = (n.innerLabel() == b.innerLabel) && (n.outerLabel() == b.outerLabel) && (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }

    @Override()
    public org.key_project.java.ast.InitArrayCreation visit(InitArrayCreation n) {
        var b = n.builder();
        b.newObjectSV = (SchemaVariable) accept(n.newObjectSV());
        b.body = (ProgramElement) accept(n.body());
        boolean clean = (n.newObjectSV() == b.newObjectSV) && (n.body() == b.body) && (n.name() == b.name) && (n.positionInfo() == b.positionInfo) && (n.hashCode() == b.hashCode);
        return clean ? n : b.build();
    }
}
