/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder;

import java.io.IOException;
import java.io.Reader;
import java.io.Writer;
import java.util.List;

import recoder.java.*;
import recoder.java.declaration.*;
import recoder.java.declaration.modifier.*;
import recoder.java.expression.ArrayInitializer;
import recoder.java.expression.ParenthesizedExpression;
import recoder.java.expression.literal.*;
import recoder.java.expression.operator.*;
import recoder.java.reference.*;
import recoder.java.statement.*;
import recoder.list.generic.ASTList;

public interface ProgramFactory extends Service {

    /**
     * Parse a {@link CompilationUnit}from the given reader.
     */
    CompilationUnit parseCompilationUnit(Reader in) throws IOException, ParserException;

    /**
     * Parse a {@link TypeDeclaration}from the given reader.
     */
    TypeDeclaration parseTypeDeclaration(Reader in) throws IOException, ParserException;

    /**
     * Parse a {@link FieldDeclaration}from the given reader.
     */
    FieldDeclaration parseFieldDeclaration(Reader in) throws IOException, ParserException;

    /**
     * Parse a {@link MethodDeclaration}from the given reader.
     */
    MethodDeclaration parseMethodDeclaration(Reader in) throws IOException, ParserException;

    /**
     * Parse a {@link MemberDeclaration}from the given reader.
     */
    MemberDeclaration parseMemberDeclaration(Reader in) throws IOException, ParserException;

    /**
     * Parse a {@link ParameterDeclaration}from the given reader.
     */
    ParameterDeclaration parseParameterDeclaration(Reader in) throws IOException, ParserException;

    /**
     * Parse a {@link ConstructorDeclaration}from the given reader.
     */
    ConstructorDeclaration parseConstructorDeclaration(Reader in)
            throws IOException, ParserException;

    /**
     * Parse a {@link TypeReference}from the given reader.
     */
    TypeReference parseTypeReference(Reader in) throws IOException, ParserException;

    /**
     * Parse an {@link Expression}from the given reader.
     */
    Expression parseExpression(Reader in) throws IOException, ParserException;

    /**
     * Parse some {@link Statement}s from the given reader.
     */
    ASTList<Statement> parseStatements(Reader in) throws IOException, ParserException;

    /**
     * Parse a {@link StatementBlock}from the given string.
     */
    StatementBlock parseStatementBlock(Reader in) throws IOException, ParserException;

    /**
     * Parse a {@link CompilationUnit}from the given string.
     */
    CompilationUnit parseCompilationUnit(String in) throws ParserException;

    /**
     * Parse {@link CompilationUnit}s from the given string.
     */
    List<CompilationUnit> parseCompilationUnits(String[] ins) throws ParserException;

    /**
     * Parse a {@link TypeDeclaration}from the given string.
     */
    TypeDeclaration parseTypeDeclaration(String in) throws ParserException;

    /**
     * Parse a {@link MemberDeclaration}from the given string.
     */
    MemberDeclaration parseMemberDeclaration(String in) throws ParserException;

    /**
     * Parse a {@link FieldDeclaration}from the given string.
     */
    FieldDeclaration parseFieldDeclaration(String in) throws ParserException;

    /**
     * Parse a {@link MethodDeclaration}from the given string.
     */
    MethodDeclaration parseMethodDeclaration(String in) throws ParserException;

    /**
     * Parse a {@link ParameterDeclaration}from the given string.
     */
    ParameterDeclaration parseParameterDeclaration(String in) throws ParserException;

    /**
     * Parse a {@link ConstructorDeclaration}from the given string.
     */
    ConstructorDeclaration parseConstructorDeclaration(String in) throws ParserException;

    /**
     * Parse a {@link TypeReference}from the given string.
     */
    TypeReference parseTypeReference(String in) throws ParserException;

    /**
     * Parse an {@link Expression}from the given string.
     */
    Expression parseExpression(String in) throws ParserException;

    /**
     * Parse a list of {@link Statement}s from the given string.
     */
    ASTList<Statement> parseStatements(String in) throws ParserException;

    /**
     * Returns a new suitable {@link recoder.java.PrettyPrinter}obeying the current project settings
     * for the specified writer,
     *
     * @param out the (initial) writer to print to.
     * @return a new pretty printer.
     */
    PrettyPrinter getPrettyPrinter(Writer out);

    /**
     * Creates a new {@link Comment}.
     *
     * @return a new instance of Comment.
     */
    Comment createComment();

    /**
     * Creates a new {@link Comment}.
     *
     * @return a new instance of Comment.
     */
    Comment createComment(String text);

    /**
     * Creates a new {@link Comment}.
     *
     * @return a new instance of Comment.
     */
    Comment createComment(String text, boolean prefixed);

    /**
     * Creates a new {@link CompilationUnit}.
     *
     * @return a new instance of CompilationUnit.
     */
    CompilationUnit createCompilationUnit();

    /**
     * Creates a new {@link CompilationUnit}.
     *
     * @return a new instance of CompilationUnit.
     */
    CompilationUnit createCompilationUnit(PackageSpecification pkg, ASTList<Import> imports,
            ASTList<TypeDeclaration> typeDeclarations);

    /**
     * Creates a new {@link DocComment}.
     *
     * @return a new instance of DocComment.
     */
    DocComment createDocComment();

    /**
     * Creates a new {@link DocComment}.
     *
     * @return a new instance of DocComment.
     */
    DocComment createDocComment(String text);

    /**
     * Creates a new {@link Identifier}.
     *
     * @return a new instance of Identifier.
     */
    Identifier createIdentifier();

    /**
     * Creates a new {@link Identifier}.
     *
     * @return a new instance of Identifier.
     */
    Identifier createIdentifier(String text);

    /**
     * Creates a new {@link Import}.
     *
     * @return a new instance of Import.
     */
    Import createImport();

    /**
     * Creates a new {@link Import}.
     *
     * @return a new instance of Import.
     */
    Import createImport(TypeReference t, boolean multi);

    /**
     * Creates a new {@link Import}.
     *
     * @return a new instance of Import.
     */
    Import createImport(PackageReference t);

    /**
     * Creates a new {@link Import}.
     *
     * @return a new instance of Import.
     */
    Import createStaticImport(TypeReference t);

    /**
     * Creates a new {@link Import}.
     *
     * @return a new instance of Import.
     */
    Import createStaticImport(TypeReference t, Identifier id);

    /**
     * Creates a new {@link PackageSpecification}.
     *
     * @return a new instance of PackageSpecification.
     */
    PackageSpecification createPackageSpecification();

    /**
     * Creates a new {@link PackageSpecification}.
     *
     * @return a new instance of PackageSpecification.
     */
    PackageSpecification createPackageSpecification(PackageReference pkg);

    /**
     * Creates a new {@link SingleLineComment}.
     *
     * @return a new instance of SingleLineComment.
     */
    SingleLineComment createSingleLineComment();

    /**
     * Creates a new {@link SingleLineComment}.
     *
     * @return a new instance of SingleLineComment.
     */
    SingleLineComment createSingleLineComment(String text);

    /**
     * Creates a new {@link TypeReference}.
     *
     * @return a new instance of TypeReference.
     */
    TypeReference createTypeReference();

    /**
     * Creates a new {@link TypeReference}.
     *
     * @return a new instance of TypeReference.
     */
    TypeReference createTypeReference(Identifier name);

    /**
     * Creates a new {@link TypeReference}.
     *
     * @return a new instance of TypeReference.
     */
    TypeReference createTypeReference(ReferencePrefix prefix, Identifier name);

    /**
     * Creates a new {@link TypeReference}.
     *
     * @return a new instance of TypeReference.
     */
    TypeReference createTypeReference(Identifier name, int dim);

    /**
     * Creates a new {@link PackageReference}.
     *
     * @return a new instance of PackageReference.
     */
    PackageReference createPackageReference();

    /**
     * Creates a new {@link PackageReference}.
     *
     * @return a new instance of PackageReference.
     */
    PackageReference createPackageReference(Identifier id);

    /**
     * Creates a new {@link PackageReference}.
     *
     * @return a new instance of PackageReference.
     */
    PackageReference createPackageReference(PackageReference path, Identifier id);

    /**
     * Creates a new {@link UncollatedReferenceQualifier}.
     *
     * @return a new instance of UncollatedReferenceQualifier.
     */
    UncollatedReferenceQualifier createUncollatedReferenceQualifier();

    /**
     * Creates a new {@link UncollatedReferenceQualifier}.
     *
     * @return a new instance of UncollatedReferenceQualifier.
     */
    UncollatedReferenceQualifier createUncollatedReferenceQualifier(Identifier id);

    /**
     * Creates a new {@link UncollatedReferenceQualifier}.
     *
     * @return a new instance of UncollatedReferenceQualifier.
     */
    UncollatedReferenceQualifier createUncollatedReferenceQualifier(ReferencePrefix prefix,
            Identifier id);

    /**
     * Creates a new {@link ClassDeclaration}.
     *
     * @return a new instance of ClassDeclaration.
     */
    ClassDeclaration createClassDeclaration();


    /**
     * Creates a new {@link ClassDeclaration}.
     *
     * @return a new instance of ClassDeclaration.
     */
    ClassDeclaration createClassDeclaration(ASTList<DeclarationSpecifier> declSpecs,
            Identifier name, Extends extended, Implements implemented,
            ASTList<MemberDeclaration> members);

    /**
     * Creates a new {@link ClassDeclaration}.
     *
     * @return a new instance of ClassDeclaration.
     */
    ClassDeclaration createClassDeclaration(ASTList<MemberDeclaration> members);

    /**
     * Creates a new {@link ClassInitializer}.
     *
     * @return a new instance of ClassInitializer.
     */
    ClassInitializer createClassInitializer();

    /**
     * Creates a new {@link ClassInitializer}.
     *
     * @return a new instance of ClassInitializer.
     */
    ClassInitializer createClassInitializer(StatementBlock body);

    /**
     * Creates a new {@link ClassInitializer}.
     *
     * @return a new instance of ClassInitializer.
     */
    ClassInitializer createClassInitializer(Static modifier, StatementBlock body);

    /**
     * Creates a new {@link ConstructorDeclaration}.
     *
     * @return a new instance of ConstructorDeclaration.
     */
    ConstructorDeclaration createConstructorDeclaration();

    /**
     * Creates a new {@link ConstructorDeclaration}.
     *
     * @return a new instance of ConstructorDeclaration.
     */
    ConstructorDeclaration createConstructorDeclaration(VisibilityModifier modifier,
            Identifier name, ASTList<ParameterDeclaration> parameters, Throws exceptions,
            StatementBlock body);

    /**
     * Creates a new {@link Throws}.
     *
     * @return a new instance of Throws.
     */
    Throws createThrows();

    /**
     * Creates a new {@link Throws}.
     *
     * @return a new instance of Throws.
     */
    Throws createThrows(TypeReference exception);

    /**
     * Creates a new {@link Throws}.
     *
     * @return a new instance of Throws.
     */
    Throws createThrows(ASTList<TypeReference> list);

    /**
     * Creates a new {@link FieldDeclaration}.
     *
     * @return a new instance of FieldDeclaration.
     */
    FieldDeclaration createFieldDeclaration();

    /**
     * Creates a new {@link FieldDeclaration}.
     *
     * @return a new instance of FieldDeclaration.
     */
    FieldDeclaration createFieldDeclaration(TypeReference typeRef, Identifier name);

    /**
     * Creates a new {@link FieldDeclaration}.
     *
     * @return a new instance of FieldDeclaration.
     */
    FieldDeclaration createFieldDeclaration(ASTList<DeclarationSpecifier> mods,
            TypeReference typeRef, Identifier name, Expression init);

    /**
     * Creates a new {@link FieldDeclaration}.
     *
     * @return a new instance of FieldDeclaration.
     */
    FieldDeclaration createFieldDeclaration(ASTList<DeclarationSpecifier> mods,
            TypeReference typeRef, ASTList<FieldSpecification> vars);

    /**
     * Creates a new {@link Extends}.
     *
     * @return a new instance of Extends.
     */
    Extends createExtends();

    /**
     * Creates a new {@link Extends}.
     *
     * @return a new instance of Extends.
     */
    Extends createExtends(TypeReference supertype);

    /**
     * Creates a new {@link Extends}.
     *
     * @return a new instance of Extends.
     */
    Extends createExtends(ASTList<TypeReference> list);

    /**
     * Creates a new {@link Implements}.
     *
     * @return a new instance of Implements.
     */
    Implements createImplements();

    /**
     * Creates a new {@link Implements}.
     *
     * @return a new instance of Implements.
     */
    Implements createImplements(TypeReference supertype);

    /**
     * Creates a new {@link Implements}.
     *
     * @return a new instance of Implements.
     */
    Implements createImplements(ASTList<TypeReference> list);

    /**
     * Creates a new {@link InterfaceDeclaration}.
     *
     * @return a new instance of InterfaceDeclaration.
     */
    InterfaceDeclaration createInterfaceDeclaration();

    /**
     * Creates a new {@link InterfaceDeclaration}.
     *
     * @return a new instance of InterfaceDeclaration.
     */
    InterfaceDeclaration createInterfaceDeclaration(ASTList<DeclarationSpecifier> modifiers,
            Identifier name, Extends extended, ASTList<MemberDeclaration> members);

    AnnotationDeclaration createAnnotationDeclaration();

    AnnotationDeclaration createAnnotationDeclaration(ASTList<DeclarationSpecifier> modifiers,
            Identifier name, ASTList<MemberDeclaration> members);

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     *
     * @return a new instance of LocalVariableDeclaration.
     */
    LocalVariableDeclaration createLocalVariableDeclaration();

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     *
     * @return a new instance of LocalVariableDeclaration.
     */
    LocalVariableDeclaration createLocalVariableDeclaration(TypeReference typeRef, Identifier name);

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     *
     * @return a new instance of LocalVariableDeclaration.
     */
    LocalVariableDeclaration createLocalVariableDeclaration(ASTList<DeclarationSpecifier> mods,
            TypeReference typeRef, ASTList<VariableSpecification> vars);

    /**
     * Creates a new {@link LocalVariableDeclaration}.
     *
     * @return a new instance of LocalVariableDeclaration.
     */
    LocalVariableDeclaration createLocalVariableDeclaration(ASTList<DeclarationSpecifier> mods,
            TypeReference typeRef, Identifier name, Expression init);


    /**
     * Creates a new {@link MethodDeclaration}.
     *
     * @return a new instance of MethodDeclaration.
     */
    MethodDeclaration createMethodDeclaration();

    /**
     * Creates a new {@link MethodDeclaration}.
     *
     * @return a new instance of MethodDeclaration.
     */
    MethodDeclaration createMethodDeclaration(ASTList<DeclarationSpecifier> modifiers,
            TypeReference returnType, Identifier name, ASTList<ParameterDeclaration> parameters,
            Throws exceptions);

    /**
     * Creates a new {@link MethodDeclaration}.
     *
     * @return a new instance of MethodDeclaration.
     */
    MethodDeclaration createMethodDeclaration(ASTList<DeclarationSpecifier> modifiers,
            TypeReference returnType, Identifier name, ASTList<ParameterDeclaration> parameters,
            Throws exceptions, StatementBlock body);

    AnnotationPropertyDeclaration createAnnotationPropertyDeclaration(
            ASTList<DeclarationSpecifier> modifiers, TypeReference returnType, Identifier name,
            Expression defaultValue);

    /**
     * Creates a new {@link ParameterDeclaration}.
     *
     * @return a new instance of ParameterDeclaration.
     */
    ParameterDeclaration createParameterDeclaration();

    /**
     * Creates a new {@link ParameterDeclaration}.
     *
     * @return a new instance of ParameterDeclaration.
     */
    ParameterDeclaration createParameterDeclaration(TypeReference typeRef, Identifier name);

    /**
     * Creates a new {@link ParameterDeclaration}.
     *
     * @return a new instance of ParameterDeclaration.
     */
    ParameterDeclaration createParameterDeclaration(ASTList<DeclarationSpecifier> mods,
            TypeReference typeRef, Identifier name);

    /**
     * Creates a new {@link VariableSpecification}.
     *
     * @return a new instance of VariableSpecification.
     */
    VariableSpecification createVariableSpecification();

    /**
     * Creates a new {@link VariableSpecification}.
     *
     * @return a new instance of VariableSpecification.
     */
    VariableSpecification createVariableSpecification(Identifier name);

    /**
     * Creates a new {@link VariableSpecification}.
     *
     * @return a new instance of VariableSpecification.
     */
    VariableSpecification createVariableSpecification(Identifier name, Expression init);

    /**
     * Creates a new {@link VariableSpecification}.
     *
     * @return a new instance of VariableSpecification.
     */
    VariableSpecification createVariableSpecification(Identifier name, int dimensions,
            Expression init);

    /**
     * Creates a new {@link FieldSpecification}.
     *
     * @return a new instance of FieldSpecification.
     */
    FieldSpecification createFieldSpecification();

    /**
     * Creates a new {@link FieldSpecification}.
     *
     * @return a new instance of FieldSpecification.
     */
    FieldSpecification createFieldSpecification(Identifier name);

    /**
     * Creates a new {@link FieldSpecification}.
     *
     * @return a new instance of FieldSpecification.
     */
    FieldSpecification createFieldSpecification(Identifier name, Expression init);

    /**
     * Creates a new {@link FieldSpecification}.
     *
     * @return a new instance of FieldSpecification.
     */
    FieldSpecification createFieldSpecification(Identifier name, int dimensions, Expression init);

    /**
     * Creates a new {@link ArrayInitializer}.
     *
     * @return a new instance of ArrayInitializer.
     */
    ArrayInitializer createArrayInitializer();

    /**
     * Creates a new {@link ArrayInitializer}.
     *
     * @return a new instance of ArrayInitializer.
     */
    ArrayInitializer createArrayInitializer(ASTList<Expression> args);

    /**
     * Creates a new {@link ParenthesizedExpression}.
     *
     * @return a new instance of ParenthesizedExpression.
     */
    ParenthesizedExpression createParenthesizedExpression();

    /**
     * Creates a new {@link ParenthesizedExpression}.
     *
     * @return a new instance of ParenthesizedExpression.
     */
    ParenthesizedExpression createParenthesizedExpression(Expression child);

    /**
     * Creates a new {@link BooleanLiteral}.
     *
     * @return a new instance of BooleanLiteral.
     */
    BooleanLiteral createBooleanLiteral();

    /**
     * Creates a new {@link BooleanLiteral}.
     *
     * @return a new instance of BooleanLiteral.
     */
    BooleanLiteral createBooleanLiteral(boolean value);

    /**
     * Creates a new {@link CharLiteral}.
     *
     * @return a new instance of CharLiteral.
     */
    CharLiteral createCharLiteral();

    /**
     * Creates a new {@link CharLiteral}.
     *
     * @return a new instance of CharLiteral.
     */
    CharLiteral createCharLiteral(char value);

    /**
     * Creates a new {@link CharLiteral}.
     *
     * @return a new instance of CharLiteral.
     */
    CharLiteral createCharLiteral(String value);

    /**
     * Creates a new {@link DoubleLiteral}.
     *
     * @return a new instance of DoubleLiteral.
     */
    DoubleLiteral createDoubleLiteral();

    /**
     * Creates a new {@link DoubleLiteral}.
     *
     * @return a new instance of DoubleLiteral.
     */
    DoubleLiteral createDoubleLiteral(double value);

    /**
     * Creates a new {@link DoubleLiteral}.
     *
     * @return a new instance of DoubleLiteral.
     */
    DoubleLiteral createDoubleLiteral(String value);

    /**
     * Creates a new {@link FloatLiteral}.
     *
     * @return a new instance of FloatLiteral.
     */
    FloatLiteral createFloatLiteral();

    /**
     * Creates a new {@link FloatLiteral}.
     *
     * @return a new instance of FloatLiteral.
     */
    FloatLiteral createFloatLiteral(float value);

    /**
     * Creates a new {@link FloatLiteral}.
     *
     * @return a new instance of FloatLiteral.
     */
    FloatLiteral createFloatLiteral(String value);

    /**
     * Creates a new {@link IntLiteral}.
     *
     * @return a new instance of IntLiteral.
     */
    IntLiteral createIntLiteral();

    /**
     * Creates a new {@link IntLiteral}.
     *
     * @return a new instance of IntLiteral.
     */
    IntLiteral createIntLiteral(int value);

    /**
     * Creates a new {@link IntLiteral}.
     *
     * @return a new instance of IntLiteral.
     */
    IntLiteral createIntLiteral(String value);

    /**
     * Creates a new {@link LongLiteral}.
     *
     * @return a new instance of LongLiteral.
     */
    LongLiteral createLongLiteral();

    /**
     * Creates a new {@link LongLiteral}.
     *
     * @return a new instance of LongLiteral.
     */
    LongLiteral createLongLiteral(long value);

    /**
     * Creates a new {@link LongLiteral}.
     *
     * @return a new instance of LongLiteral.
     */
    LongLiteral createLongLiteral(String value);

    /**
     * Creates a new {@link NullLiteral}.
     *
     * @return a new instance of NullLiteral.
     */
    NullLiteral createNullLiteral();

    /**
     * Creates a new {@link StringLiteral}.
     *
     * @return a new instance of StringLiteral.
     */
    StringLiteral createStringLiteral();

    /**
     * Creates a new {@link StringLiteral}.
     *
     * @return a new instance of StringLiteral.
     */
    StringLiteral createStringLiteral(String value);

    /**
     * Creates a new {@link ArrayReference}.
     *
     * @return a new instance of ArrayReference.
     */
    ArrayReference createArrayReference();

    /**
     * Creates a new {@link ArrayReference}.
     *
     * @return a new instance of ArrayReference.
     */
    ArrayReference createArrayReference(ReferencePrefix accessPath,
            ASTList<Expression> initializers);

    /**
     * Creates a new {@link FieldReference}.
     *
     * @return a new instance of FieldReference.
     */
    FieldReference createFieldReference();

    /**
     * Creates a new {@link FieldReference}.
     *
     * @return a new instance of FieldReference.
     */
    FieldReference createFieldReference(Identifier id);

    /**
     * Creates a new {@link FieldReference}.
     *
     * @return a new instance of FieldReference.
     */
    FieldReference createFieldReference(ReferencePrefix prefix, Identifier id);

    /**
     * Creates a new {@link MetaClassReference}.
     *
     * @return a new instance of MetaClassReference.
     */
    MetaClassReference createMetaClassReference();

    /**
     * Creates a new {@link MetaClassReference}.
     *
     * @return a new instance of MetaClassReference.
     */
    MetaClassReference createMetaClassReference(TypeReference reference);

    /**
     * Creates a new {@link MethodReference}.
     *
     * @return a new instance of MethodReference.
     */
    MethodReference createMethodReference();

    /**
     * Creates a new {@link MethodReference}.
     *
     * @return a new instance of MethodReference.
     */
    MethodReference createMethodReference(Identifier name);

    /**
     * Creates a new {@link MethodReference}.
     *
     * @return a new instance of MethodReference.
     */
    MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name);

    /**
     * Creates a new {@link MethodReference}.
     *
     * @return a new instance of MethodReference.
     */
    MethodReference createMethodReference(Identifier name, ASTList<Expression> args);

    /**
     * Creates a new {@link MethodReference}.
     *
     * @return a new instance of MethodReference.
     */
    MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name,
            ASTList<Expression> args);

    MethodReference createMethodReference(ReferencePrefix accessPath, Identifier name,
            ASTList<Expression> args, ASTList<TypeArgumentDeclaration> typeArgs);


    AnnotationPropertyReference createAnnotationPropertyReference(String id);

    AnnotationPropertyReference createAnnotationPropertyReference(Identifier id);

    /**
     * Creates a new {@link SuperConstructorReference}.
     *
     * @return a new instance of SuperConstructorReference.
     */
    SuperConstructorReference createSuperConstructorReference();

    /**
     * Creates a new {@link SuperConstructorReference}.
     *
     * @return a new instance of SuperConstructorReference.
     */
    SuperConstructorReference createSuperConstructorReference(ASTList<Expression> arguments);

    /**
     * Creates a new {@link SuperConstructorReference}.
     *
     * @return a new instance of SuperConstructorReference.
     */
    SuperConstructorReference createSuperConstructorReference(ReferencePrefix path,
            ASTList<Expression> arguments);

    /**
     * Creates a new {@link SuperReference}.
     *
     * @return a new instance of SuperReference.
     */
    SuperReference createSuperReference();

    /**
     * Creates a new {@link SuperReference}.
     *
     * @return a new instance of SuperReference.
     */
    SuperReference createSuperReference(ReferencePrefix accessPath);

    /**
     * Creates a new {@link ThisConstructorReference}.
     *
     * @return a new instance of ThisConstructorReference.
     */
    ThisConstructorReference createThisConstructorReference();

    /**
     * Creates a new {@link ThisConstructorReference}.
     *
     * @return a new instance of ThisConstructorReference.
     */
    ThisConstructorReference createThisConstructorReference(ASTList<Expression> arguments);

    /**
     * Creates a new {@link ThisReference}.
     *
     * @return a new instance of ThisReference.
     */
    ThisReference createThisReference();

    /**
     * Creates a new {@link ThisReference}.
     *
     * @return a new instance of ThisReference.
     */
    ThisReference createThisReference(TypeReference outer);

    /**
     * Creates a new {@link VariableReference}.
     *
     * @return a new instance of VariableReference.
     */
    VariableReference createVariableReference();

    /**
     * Creates a new {@link VariableReference}.
     *
     * @return a new instance of VariableReference.
     */
    VariableReference createVariableReference(Identifier id);

    /**
     * Creates a new {@link ArrayLengthReference}.
     *
     * @return a new instance of ArrayLengthReference.
     */
    ArrayLengthReference createArrayLengthReference();

    /**
     * Creates a new {@link ArrayLengthReference}.
     *
     * @return a new instance of ArrayLengthReference.
     */
    ArrayLengthReference createArrayLengthReference(ReferencePrefix prefix);

    /**
     * Creates a new {@link BinaryAnd}.
     *
     * @return a new instance of BinaryAnd.
     */
    BinaryAnd createBinaryAnd();

    /**
     * Creates a new {@link BinaryAnd}.
     *
     * @return a new instance of BinaryAnd.
     */
    BinaryAnd createBinaryAnd(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link BinaryAndAssignment}.
     *
     * @return a new instance of BinaryAndAssignment.
     */
    BinaryAndAssignment createBinaryAndAssignment();

    /**
     * Creates a new {@link BinaryAndAssignment}.
     *
     * @return a new instance of BinaryAndAssignment.
     */
    BinaryAndAssignment createBinaryAndAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link BinaryNot}.
     *
     * @return a new instance of BinaryNot.
     */
    BinaryNot createBinaryNot();

    /**
     * Creates a new {@link BinaryNot}.
     *
     * @return a new instance of BinaryNot.
     */
    BinaryNot createBinaryNot(Expression child);

    /**
     * Creates a new {@link BinaryOr}.
     *
     * @return a new instance of BinaryOr.
     */
    BinaryOr createBinaryOr();

    /**
     * Creates a new {@link BinaryOr}.
     *
     * @return a new instance of BinaryOr.
     */
    BinaryOr createBinaryOr(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link BinaryOrAssignment}.
     *
     * @return a new instance of BinaryOrAssignment.
     */
    BinaryOrAssignment createBinaryOrAssignment();

    /**
     * Creates a new {@link BinaryOrAssignment}.
     *
     * @return a new instance of BinaryOrAssignment.
     */
    BinaryOrAssignment createBinaryOrAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link BinaryXOr}.
     *
     * @return a new instance of BinaryXOr.
     */
    BinaryXOr createBinaryXOr();

    /**
     * Creates a new {@link BinaryXOr}.
     *
     * @return a new instance of BinaryXOr.
     */
    BinaryXOr createBinaryXOr(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link BinaryXOrAssignment}.
     *
     * @return a new instance of BinaryXOrAssignment.
     */
    BinaryXOrAssignment createBinaryXOrAssignment();

    /**
     * Creates a new {@link BinaryXOrAssignment}.
     *
     * @return a new instance of BinaryXOrAssignment.
     */
    BinaryXOrAssignment createBinaryXOrAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link Conditional}.
     *
     * @return a new instance of Conditional.
     */
    Conditional createConditional();

    /**
     * Creates a new {@link Conditional}.
     *
     * @return a new instance of Conditional.
     */
    Conditional createConditional(Expression guard, Expression thenExpr, Expression elseExpr);

    /**
     * Creates a new {@link CopyAssignment}.
     *
     * @return a new instance of CopyAssignment.
     */
    CopyAssignment createCopyAssignment();

    /**
     * Creates a new {@link CopyAssignment}.
     *
     * @return a new instance of CopyAssignment.
     */
    CopyAssignment createCopyAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link Divide}.
     *
     * @return a new instance of Divide.
     */
    Divide createDivide();

    /**
     * Creates a new {@link Divide}.
     *
     * @return a new instance of Divide.
     */
    Divide createDivide(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link DivideAssignment}.
     *
     * @return a new instance of DivideAssignment.
     */
    DivideAssignment createDivideAssignment();

    /**
     * Creates a new {@link DivideAssignment}.
     *
     * @return a new instance of DivideAssignment.
     */
    DivideAssignment createDivideAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link Equals}.
     *
     * @return a new instance of Equals.
     */
    Equals createEquals();

    /**
     * Creates a new {@link Equals}.
     *
     * @return a new instance of Equals.
     */
    Equals createEquals(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link GreaterOrEquals}.
     *
     * @return a new instance of GreaterOrEquals.
     */
    GreaterOrEquals createGreaterOrEquals();

    /**
     * Creates a new {@link GreaterOrEquals}.
     *
     * @return a new instance of GreaterOrEquals.
     */
    GreaterOrEquals createGreaterOrEquals(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link GreaterThan}.
     *
     * @return a new instance of GreaterThan.
     */
    GreaterThan createGreaterThan();

    /**
     * Creates a new {@link GreaterThan}.
     *
     * @return a new instance of GreaterThan.
     */
    GreaterThan createGreaterThan(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link Instanceof}.
     *
     * @return a new instance of Instanceof.
     */
    Instanceof createInstanceof();

    /**
     * Creates a new {@link Instanceof}.
     *
     * @return a new instance of Instanceof.
     */
    Instanceof createInstanceof(Expression child, TypeReference typeref);

    /**
     * Creates a new {@link LessOrEquals}.
     *
     * @return a new instance of LessOrEquals.
     */
    LessOrEquals createLessOrEquals();

    /**
     * Creates a new {@link LessOrEquals}.
     *
     * @return a new instance of LessOrEquals.
     */
    LessOrEquals createLessOrEquals(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link LessThan}.
     *
     * @return a new instance of LessThan.
     */
    LessThan createLessThan();

    /**
     * Creates a new {@link LessThan}.
     *
     * @return a new instance of LessThan.
     */
    LessThan createLessThan(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link LogicalAnd}.
     *
     * @return a new instance of LogicalAnd.
     */
    LogicalAnd createLogicalAnd();

    /**
     * Creates a new {@link LogicalAnd}.
     *
     * @return a new instance of LogicalAnd.
     */
    LogicalAnd createLogicalAnd(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link LogicalNot}.
     *
     * @return a new instance of LogicalNot.
     */
    LogicalNot createLogicalNot();

    /**
     * Creates a new {@link LogicalNot}.
     *
     * @return a new instance of LogicalNot.
     */
    LogicalNot createLogicalNot(Expression child);

    /**
     * Creates a new {@link LogicalOr}.
     *
     * @return a new instance of LogicalOr.
     */
    LogicalOr createLogicalOr();

    /**
     * Creates a new {@link LogicalOr}.
     *
     * @return a new instance of LogicalOr.
     */
    LogicalOr createLogicalOr(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link Minus}.
     *
     * @return a new instance of Minus.
     */
    Minus createMinus();

    /**
     * Creates a new {@link Minus}.
     *
     * @return a new instance of Minus.
     */
    Minus createMinus(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link MinusAssignment}.
     *
     * @return a new instance of MinusAssignment.
     */
    MinusAssignment createMinusAssignment();

    /**
     * Creates a new {@link MinusAssignment}.
     *
     * @return a new instance of MinusAssignment.
     */
    MinusAssignment createMinusAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link Modulo}.
     *
     * @return a new instance of Modulo.
     */
    Modulo createModulo();

    /**
     * Creates a new {@link Modulo}.
     *
     * @return a new instance of Modulo.
     */
    Modulo createModulo(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link ModuloAssignment}.
     *
     * @return a new instance of ModuloAssignment.
     */
    ModuloAssignment createModuloAssignment();

    /**
     * Creates a new {@link ModuloAssignment}.
     *
     * @return a new instance of ModuloAssignment.
     */
    ModuloAssignment createModuloAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link Negative}.
     *
     * @return a new instance of Negative.
     */
    Negative createNegative();

    /**
     * Creates a new {@link Negative}.
     *
     * @return a new instance of Negative.
     */
    Negative createNegative(Expression child);

    /**
     * Creates a new {@link New}.
     *
     * @return a new instance of New.
     */
    New createNew();

    /**
     * Creates a new {@link New}.
     *
     * @return a new instance of New.
     */
    New createNew(ReferencePrefix accessPath, TypeReference constructorName,
            ASTList<Expression> arguments);

    /**
     * Creates a new {@link New}.
     *
     * @return a new instance of New.
     */
    New createNew(ReferencePrefix accessPath, TypeReference constructorName,
            ASTList<Expression> arguments, ClassDeclaration anonymousClass);

    /**
     * Creates a new {@link NewArray}.
     *
     * @return a new instance of NewArray.
     */
    NewArray createNewArray();

    /**
     * Creates a new {@link NewArray}.
     *
     * @return a new instance of NewArray.
     */
    NewArray createNewArray(TypeReference arrayName, ASTList<Expression> dimExpr);

    /**
     * Creates a new {@link NewArray}.
     *
     * @return a new instance of NewArray.
     */
    NewArray createNewArray(TypeReference arrayName, int dimensions, ArrayInitializer initializer);

    /**
     * Creates a new {@link NotEquals}.
     *
     * @return a new instance of NotEquals.
     */
    NotEquals createNotEquals();

    /**
     * Creates a new {@link NotEquals}.
     *
     * @return a new instance of NotEquals.
     */
    NotEquals createNotEquals(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link Plus}.
     *
     * @return a new instance of Plus.
     */
    Plus createPlus();

    /**
     * Creates a new {@link Plus}.
     *
     * @return a new instance of Plus.
     */
    Plus createPlus(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link PlusAssignment}.
     *
     * @return a new instance of PlusAssignment.
     */
    PlusAssignment createPlusAssignment();

    /**
     * Creates a new {@link PlusAssignment}.
     *
     * @return a new instance of PlusAssignment.
     */
    PlusAssignment createPlusAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link Positive}.
     *
     * @return a new instance of Positive.
     */
    Positive createPositive();

    /**
     * Creates a new {@link Positive}.
     *
     * @return a new instance of Positive.
     */
    Positive createPositive(Expression child);

    /**
     * Creates a new {@link PostDecrement}.
     *
     * @return a new instance of PostDecrement.
     */
    PostDecrement createPostDecrement();

    /**
     * Creates a new {@link PostDecrement}.
     *
     * @return a new instance of PostDecrement.
     */
    PostDecrement createPostDecrement(Expression child);

    /**
     * Creates a new {@link PostIncrement}.
     *
     * @return a new instance of PostIncrement.
     */
    PostIncrement createPostIncrement();

    /**
     * Creates a new {@link PostIncrement}.
     *
     * @return a new instance of PostIncrement.
     */
    PostIncrement createPostIncrement(Expression child);

    /**
     * Creates a new {@link PreDecrement}.
     *
     * @return a new instance of PreDecrement.
     */
    PreDecrement createPreDecrement();

    /**
     * Creates a new {@link PreDecrement}.
     *
     * @return a new instance of PreDecrement.
     */
    PreDecrement createPreDecrement(Expression child);

    /**
     * Creates a new {@link PreIncrement}.
     *
     * @return a new instance of PreIncrement.
     */
    PreIncrement createPreIncrement();

    /**
     * Creates a new {@link PreIncrement}.
     *
     * @return a new instance of PreIncrement.
     */
    PreIncrement createPreIncrement(Expression child);

    /**
     * Creates a new {@link ShiftLeft}.
     *
     * @return a new instance of ShiftLeft.
     */
    ShiftLeft createShiftLeft();

    /**
     * Creates a new {@link ShiftLeft}.
     *
     * @return a new instance of ShiftLeft.
     */
    ShiftLeft createShiftLeft(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link ShiftLeftAssignment}.
     *
     * @return a new instance of ShiftLeftAssignment.
     */
    ShiftLeftAssignment createShiftLeftAssignment();

    /**
     * Creates a new {@link ShiftLeftAssignment}.
     *
     * @return a new instance of ShiftLeftAssignment.
     */
    ShiftLeftAssignment createShiftLeftAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link ShiftRight}.
     *
     * @return a new instance of ShiftRight.
     */
    ShiftRight createShiftRight();

    /**
     * Creates a new {@link ShiftRight}.
     *
     * @return a new instance of ShiftRight.
     */
    ShiftRight createShiftRight(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link ShiftRightAssignment}.
     *
     * @return a new instance of ShiftRightAssignment.
     */
    ShiftRightAssignment createShiftRightAssignment();

    /**
     * Creates a new {@link ShiftRightAssignment}.
     *
     * @return a new instance of ShiftRightAssignment.
     */
    ShiftRightAssignment createShiftRightAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link Times}.
     *
     * @return a new instance of Times.
     */
    Times createTimes();

    /**
     * Creates a new {@link Times}.
     *
     * @return a new instance of Times.
     */
    Times createTimes(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link TimesAssignment}.
     *
     * @return a new instance of TimesAssignment.
     */
    TimesAssignment createTimesAssignment();

    /**
     * Creates a new {@link TimesAssignment}.
     *
     * @return a new instance of TimesAssignment.
     */
    TimesAssignment createTimesAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link TypeCast}.
     *
     * @return a new instance of TypeCast.
     */
    TypeCast createTypeCast();

    /**
     * Creates a new {@link TypeCast}.
     *
     * @return a new instance of TypeCast.
     */
    TypeCast createTypeCast(Expression child, TypeReference typeref);

    /**
     * Creates a new {@link UnsignedShiftRight}.
     *
     * @return a new instance of UnsignedShiftRight.
     */
    UnsignedShiftRight createUnsignedShiftRight();

    /**
     * Creates a new {@link UnsignedShiftRight}.
     *
     * @return a new instance of UnsignedShiftRight.
     */
    UnsignedShiftRight createUnsignedShiftRight(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link UnsignedShiftRightAssignment}.
     *
     * @return a new instance of UnsignedShiftRightAssignment.
     */
    UnsignedShiftRightAssignment createUnsignedShiftRightAssignment();

    /**
     * Creates a new {@link UnsignedShiftRightAssignment}.
     *
     * @return a new instance of UnsignedShiftRightAssignment.
     */
    UnsignedShiftRightAssignment createUnsignedShiftRightAssignment(Expression lhs, Expression rhs);

    /**
     * Creates a new {@link Abstract}.
     *
     * @return a new instance of Abstract.
     */
    Abstract createAbstract();

    /**
     * Creates a new {@link Final}.
     *
     * @return a new instance of Final.
     */
    Final createFinal();

    /**
     * Creates a new {@link Native}.
     *
     * @return a new instance of Native.
     */
    Native createNative();

    /**
     * Creates a new {@link Private}.
     *
     * @return a new instance of Private.
     */
    Private createPrivate();

    /**
     * Creates a new {@link Protected}.
     *
     * @return a new instance of Protected.
     */
    Protected createProtected();

    /**
     * Creates a new {@link Public}.
     *
     * @return a new instance of Public.
     */
    Public createPublic();

    /**
     * Creates a new {@link Static}.
     *
     * @return a new instance of Static.
     */
    Static createStatic();

    /**
     * Creates a new {@link Synchronized}.
     *
     * @return a new instance of Synchronized.
     */
    Synchronized createSynchronized();

    /**
     * Creates a new {@link Transient}.
     *
     * @return a new instance of Transient.
     */
    Transient createTransient();

    /**
     * Creates a new {@link StrictFp}.
     *
     * @return a new instance of StrictFp.
     */
    StrictFp createStrictFp();

    /**
     * Creates a new {@link Volatile}.
     *
     * @return a new instance of Volatile.
     */
    Volatile createVolatile();

    /**
     * Creates a new {@ling Annotation}.
     *
     * @return a new instance of Annotation
     */
    AnnotationUseSpecification createAnnotationUseSpecification();

    /**
     * Creates a new {@link Break}.
     *
     * @return a new instance of Break.
     */
    Break createBreak();

    /**
     * Creates a new {@link Break}.
     *
     * @return a new instance of Break.
     */
    Break createBreak(Identifier label);

    /**
     * Creates a new {@link Case}.
     *
     * @return a new instance of Case.
     */
    Case createCase();

    /**
     * Creates a new {@link Case}.
     *
     * @return a new instance of Case.
     */
    Case createCase(Expression e);

    /**
     * Creates a new {@link Case}.
     *
     * @return a new instance of Case.
     */
    Case createCase(Expression e, ASTList<Statement> body);

    /**
     * Creates a new {@link Catch}.
     *
     * @return a new instance of Catch.
     */
    Catch createCatch();

    /**
     * Creates a new {@link Catch}.
     *
     * @return a new instance of Catch.
     */
    Catch createCatch(ParameterDeclaration e, StatementBlock body);

    /**
     * Creates a new {@link Continue}.
     *
     * @return a new instance of Continue.
     */
    Continue createContinue();

    /**
     * Creates a new {@link Continue}.
     *
     * @return a new instance of Continue.
     */
    Continue createContinue(Identifier label);

    /**
     * Creates a new {@link Default}.
     *
     * @return a new instance of Default.
     */
    Default createDefault();

    /**
     * Creates a new {@link Default}.
     *
     * @return a new instance of Default.
     */
    Default createDefault(ASTList<Statement> body);

    /**
     * Creates a new {@link Do}.
     *
     * @return a new instance of Do.
     */
    Do createDo();

    /**
     * Creates a new {@link Do}.
     *
     * @return a new instance of Do.
     */
    Do createDo(Expression guard);

    /**
     * Creates a new {@link Do}.
     *
     * @return a new instance of Do.
     */
    Do createDo(Expression guard, Statement body);

    /**
     * Creates a new {@link Else}.
     *
     * @return a new instance of Else.
     */
    Else createElse();

    /**
     * Creates a new {@link Else}.
     *
     * @return a new instance of Else.
     */
    Else createElse(Statement body);

    /**
     * Creates a new {@link EmptyStatement}.
     *
     * @return a new instance of EmptyStatement.
     */
    EmptyStatement createEmptyStatement();

    /**
     * Creates a new {@link Finally}.
     *
     * @return a new instance of Finally.
     */
    Finally createFinally();

    /**
     * Creates a new {@link Finally}.
     *
     * @return a new instance of Finally.
     */
    Finally createFinally(StatementBlock body);

    /**
     * Creates a new {@link For}.
     *
     * @return a new instance of For.
     */
    For createFor();

    /**
     * Creates a new {@link For}.
     *
     * @return a new instance of For.
     */
    For createFor(ASTList<LoopInitializer> inits, Expression guard, ASTList<Expression> updates,
            Statement body);


    /**
     * Creates a new {@ling EnhancedFor}.
     *
     * @return a new instance of EnhancedFor.
     */
    EnhancedFor createEnhancedFor();

    /**
     * Creates a new {@link Assert}.
     *
     * @return a new instance of Assert.
     */
    Assert createAssert();

    /**
     * Creates a new {@link Assert}.
     *
     * @return a new instance of Assert.
     */
    Assert createAssert(Expression cond);

    /**
     * Creates a new {@link Assert}.
     *
     * @return a new instance of Assert.
     */
    Assert createAssert(Expression cond, Expression msg);

    /**
     * Creates a new {@link If}.
     *
     * @return a new instance of If.
     */
    If createIf();

    /**
     * Creates a new {@link If}.
     *
     * @return a new instance of If.
     */
    If createIf(Expression e, Statement thenStatement);

    /**
     * Creates a new {@link If}.
     *
     * @return a new instance of If.
     */
    If createIf(Expression e, Then thenBranch);

    /**
     * Creates a new {@link If}.
     *
     * @return a new instance of If.
     */
    If createIf(Expression e, Then thenBranch, Else elseBranch);

    /**
     * Creates a new {@link If}.
     *
     * @return a new instance of If.
     */
    If createIf(Expression e, Statement thenStatement, Statement elseStatement);

    /**
     * Creates a new {@link LabeledStatement}.
     *
     * @return a new instance of LabeledStatement.
     */
    LabeledStatement createLabeledStatement();

    /**
     * Creates a new {@link LabeledStatement}.
     *
     * @return a new instance of LabeledStatement.
     */
    LabeledStatement createLabeledStatement(Identifier id);

    /**
     * Creates a new {@link LabeledStatement}.
     *
     * @return a new instance of LabeledStatement.
     */
    LabeledStatement createLabeledStatement(Identifier id, Statement statement);

    /**
     * Creates a new {@link Return}.
     *
     * @return a new instance of Return.
     */
    Return createReturn();

    /**
     * Creates a new {@link Return}.
     *
     * @return a new instance of Return.
     */
    Return createReturn(Expression expr);

    /**
     * Creates a new {@link StatementBlock}.
     *
     * @return a new instance of StatementBlock.
     */
    StatementBlock createStatementBlock();

    /**
     * Creates a new {@link StatementBlock}.
     *
     * @return a new instance of StatementBlock.
     */
    StatementBlock createStatementBlock(ASTList<Statement> block);

    /**
     * Creates a new {@link Switch}.
     *
     * @return a new instance of Switch.
     */
    Switch createSwitch();

    /**
     * Creates a new {@link Switch}.
     *
     * @return a new instance of Switch.
     */
    Switch createSwitch(Expression e);

    /**
     * Creates a new {@link Switch}.
     *
     * @return a new instance of Switch.
     */
    Switch createSwitch(Expression e, ASTList<Branch> branches);

    /**
     * Creates a new {@link SynchronizedBlock}.
     *
     * @return a new instance of SynchronizedBlock.
     */
    SynchronizedBlock createSynchronizedBlock();

    /**
     * Creates a new {@link SynchronizedBlock}.
     *
     * @return a new instance of SynchronizedBlock.
     */
    SynchronizedBlock createSynchronizedBlock(StatementBlock body);

    /**
     * Creates a new {@link SynchronizedBlock}.
     *
     * @return a new instance of SynchronizedBlock.
     */
    SynchronizedBlock createSynchronizedBlock(Expression e, StatementBlock body);

    /**
     * Creates a new {@link Then}.
     *
     * @return a new instance of Then.
     */
    Then createThen();

    /**
     * Creates a new {@link Then}.
     *
     * @return a new instance of Then.
     */
    Then createThen(Statement body);

    /**
     * Creates a new {@link Throw}.
     *
     * @return a new instance of Throw.
     */
    Throw createThrow();

    /**
     * Creates a new {@link Throw}.
     *
     * @return a new instance of Throw.
     */
    Throw createThrow(Expression expr);

    /**
     * Creates a new {@link Try}.
     *
     * @return a new instance of Try.
     */
    Try createTry();

    /**
     * Creates a new {@link Try}.
     *
     * @return a new instance of Try.
     */
    Try createTry(StatementBlock body);

    /**
     * Creates a new {@link Try}.
     *
     * @return a new instance of Try.
     */
    Try createTry(StatementBlock body, ASTList<Branch> branches);

    /**
     * Creates a new {@link While}.
     *
     * @return a new instance of While.
     */
    While createWhile();

    /**
     * Creates a new {@link While}.
     *
     * @return a new instance of While.
     */
    While createWhile(Expression guard);

    /**
     * Creates a new {@link While}.
     *
     * @return a new instance of While.
     */
    While createWhile(Expression guard, Statement body);
}
