/* This file was part of the RECODER library and protected by the LGPL.
 * This file is part of KeY since 2021 - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package recoder.service;

import java.util.List;

import recoder.abstraction.*;
import recoder.abstraction.Package;
import recoder.java.Expression;
import recoder.java.ProgramElement;
import recoder.java.Reference;
import recoder.java.Statement;
import recoder.java.declaration.*;
import recoder.java.reference.*;
import recoder.java.statement.EmptyStatement;
import recoder.util.ProgressListener;

/**
 * Implements queries for program model elements with concrete syntactical representations.
 *
 * @author RN, AL
 */
public interface SourceInfo extends ProgramModelInfo {

    /**
     * This is a pseudo-statement representing the exit of a method as returned by
     * {@link #getSucceedingStatements}.
     *
     * @since 0.71
     */
    Statement METHOD_EXIT = new EmptyStatement();

    /**
     * Returns the class type that contains the given program element.
     *
     * @param context a program element.
     * @return the type to which the given program element belongs (may be <CODE>null</CODE>).
     */
    ClassType getContainingClassType(ProgramElement context);

    /**
     * Returns the referred package.
     *
     * @param r a package reference.
     * @return the referred package (may be <CODE>null</CODE>).
     */
    Package getPackage(PackageReference r);

    /**
     * Returns the type for the given program element.
     *
     * @param pe the program element to compute the type for.
     * @return the type for that object (may be <CODE>null</CODE>).
     */
    Type getType(ProgramElement pe);

    /**
     * Returns the referred type.
     *
     * @param tr a type reference.
     * @return the referred type (may be <CODE>null</CODE>).
     */
    Type getType(TypeReference tr);

    /**
     * Returns the declared type.
     *
     * @param td a type declaration.
     * @return the corresponding type.
     */
    ClassType getType(TypeDeclaration td);

    /**
     * Returns the type for the variable specification. Implementors should ensure that, if
     * <code>vs</code> is an <code>EnumConstantSpecification</code>, the call is delegated to
     * <code>getType(VariableDefinition)</code>.
     *
     * @param vs a variable specification.
     * @return the type for that variable (may be <CODE>null</CODE>).
     */
    Type getType(VariableSpecification vs);

    /**
     * Tries to find a type with the given name using the given program element as context. Useful
     * to check for name clashes when introducing a new identifier. Neither name nor context may be
     * <CODE>null</CODE>.
     *
     * @param name the name for the type to be looked up; may or may not be qualified.
     * @param context a program element defining the lookup context (scope).
     * @return the corresponding type (may be <CODE>null</CODE>).
     */
    Type getType(String name, ProgramElement context);

    /**
     * Returns the type of the given expression (may be <CODE>null</CODE>).
     *
     * @param expr an expression.
     * @return the type of the expression, or <CODE>null</CODE> if the type could not be computed.
     */
    Type getType(Expression expr);

    /**
     * Checks automatic narrowing from compile-time constant ints to byte, char, or short. Returns
     * false if the primitive type is not one of byte, char, short, or if the expression is not a
     * compile-time constant int as defined in the Java language specification.
     *
     * @param expr the expression that might be a compile-time constant fitting into the given type.
     * @param to the type that the expression might fit into.
     * @return <CODE>true</CODE> if the expression value is "constant" and would fit into a variable
     *         of the given type without loss of information, <CODE>false</CODE> in any other case.
     */
    boolean isNarrowingTo(Expression expr, PrimitiveType to);

    /**
     * Tries to find a variable with the given name using the given program element as context. The
     * variable may be a local variable, a parameter or a field. Useful to check for name clashes
     * when introducing a new identifier.
     *
     * @param name the name of the variable to be looked up.
     * @param context a program element defining the lookup context.
     * @return the corresponding variable (may be <CODE>null</CODE>).
     */
    Variable getVariable(String name, ProgramElement context);

    /**
     * Returns the declared variable.
     *
     * @param vs a variable definition.
     * @return the corresponding variable.
     */
    Variable getVariable(VariableSpecification vs);

    /**
     * Returns the referred variable.
     *
     * @param vr a variable reference.
     * @return the referred variable (may be <CODE>null</CODE>).
     */
    Variable getVariable(VariableReference vr);

    /**
     * Returns the referred field.
     *
     * @param fr a field reference.
     * @return the referred field (may be <CODE>null</CODE>).
     */
    Field getField(FieldReference fr);

    /**
     * Returns the locally defined fields of the given type declaration. This method does not report
     * inherited fields. The returned list matches the syntactic order of the declarations.
     *
     * @param td a type declaration.
     * @return a list of fields that are members of the declaration.
     * @see ProgramModelInfo#getFields
     * @see ProgramModelInfo#getAllFields
     */
    List<FieldSpecification> getFields(TypeDeclaration td);

    /**
     * Returns the locally defined inner types of the given type declaration. This method does not
     * report inherited types. The returned list matches the syntactic order of the declarations.
     *
     * @param td a type declaration.
     * @return a list of inner types that are members of the declaration.
     * @see ProgramModelInfo#getTypes
     * @see ProgramModelInfo#getAllTypes
     */
    List<TypeDeclaration> getTypes(TypeDeclaration td);

    /**
     * Returns the declared method.
     *
     * @param md a method declaration.
     * @return the corresponding method.
     */
    Method getMethod(MethodDeclaration md);

    /**
     * Returns the locally defined methods of the given type declaration. This method does not
     * report inherited methods. The returned list matches the syntactic order of the declarations.
     * If td is an enum declaration, implicit members are also added.
     *
     * @param td a type declaration.
     * @return a list of methods that are members of the declaration.
     * @see ProgramModelInfo#getMethods
     * @see ProgramModelInfo#getAllMethods
     */
    List<Method> getMethods(TypeDeclaration td);

    /**
     * Returns the referred method, if there is an unambiguous one.
     *
     * @param mr the method reference to collate.
     * @return the referred method.
     * @throws AmbiguousReferenceException if there are no single most specific applicable method.
     * @throws UnresolvedReferenceException if there are no applicable method.
     * @see #getMethods(MethodReference)
     */
    Method getMethod(MethodReference mr);

    AnnotationProperty getAnnotationProperty(AnnotationPropertyReference apr);

    /**
     * Returns all methods that are applicable with respect to the given reference. Only the most
     * specific methods are returned; the program is not semantically correct if there is more than
     * one such method.
     *
     * @param mr the method reference to collate.
     * @return the list of applicable methods.
     * @see #getMethod(MethodReference)
     */
    List<Method> getMethods(MethodReference mr);

    /**
     * Returns the declared constructor.
     *
     * @param cd a constructor declaration.
     * @return the corresponding constructor.
     */
    Constructor getConstructor(ConstructorDeclaration cd);

    /**
     * Returns the locally defined constructors of the given type declaration. The returned list
     * matches the syntactic order of the declarations. This method always returns a non-empty list,
     * at least containing a {@link recoder.abstraction.DefaultConstructor}.
     *
     * @param td a type declaration.
     * @return a list of constructors that are members of the declaration.
     * @see ProgramModelInfo#getConstructors
     */
    List<Constructor> getConstructors(TypeDeclaration td);

    /**
     * Returns the referred constructor, if there is an unambiguous one.
     *
     * @param cr the constructor reference to collate.
     * @return the constructor referred.
     * @throws AmbiguousReferenceException if there are is no most specific applicable constructor.
     * @throws UnresolvedReferenceException if there are no applicable constructor.
     * @see #getConstructors(ConstructorReference)
     */
    Constructor getConstructor(ConstructorReference cr);

    /**
     * Returns all constructors that are applicable with respect to the given reference. Only the
     * most specific constructors are returned; the program is not semantically correct if there is
     * more than one such constructor.
     *
     * @param cr the constructor reference to collate.
     * @return the list of applicable constructors.
     * @see #getConstructor(ConstructorReference)
     */
    List<? extends Constructor> getConstructors(ConstructorReference cr);

    /**
     * Creates a signature by resolving the types of the given expression list. An empty or
     * <CODE>null</CODE> expression list results in an empty type list.
     *
     * @param args a list of expressions (may be <CODE>null</CODE>).
     * @return a list of types that correspond to the respective expressions.
     */
    List<Type> makeSignature(List<Expression> args);

    /**
     * Replaces the uncollated qualifier by its proper counterpart. Returns <CODE>null</CODE>, if
     * this was not possible, the replaced reference otherwise. Note that this method does not
     * notify the change history of the change!
     *
     * @param urq an uncollated reference.
     * @return a resolved reference, or <CODE>null</CODE> if the reference could not be resolved.
     */
    Reference resolveURQ(UncollatedReferenceQualifier urq);

    /**
     * Check in a program element and built up all scopes.
     *
     * @param pe the root of a syntax tree that shall be analyzed.
     * @deprecated this method will not be public in future - use ChangeHistory.attach instead
     */
    @Deprecated
    void register(ProgramElement pe);

    /**
     * Returns the syntactical counterpart of the given classtype. Returns <CODE>null</CODE>, if the
     * given type is not a type declaration.
     *
     * @param ct a class type.
     * @return the corresponding type declaration, or <CODE>null</CODE>, if the given type has no
     *         syntactical representation.
     */
    TypeDeclaration getTypeDeclaration(ClassType ct);

    /**
     * Returns the syntactical counterpart of the given method. Returns <CODE>
     * null</CODE>, if the given method is not a method declaration.
     *
     * @param m a method.
     * @return the corresponding method declaration, or <CODE>null</CODE>, if the given method has
     *         no syntactical representation.
     */
    MethodDeclaration getMethodDeclaration(Method m);

    /**
     * Returns the syntactical counterpart of the given method. Returns <CODE>
     * null</CODE>, if the given method is not a method declaration.
     *
     * @param m a method.
     * @return the corresponding method declaration, or <CODE>null</CODE>, if the given method has
     *         no syntactical representation.
     */
    ConstructorDeclaration getConstructorDeclaration(Constructor c);

    /**
     * Returns the syntactical counterpart of the given variable. Returns <CODE>
     * null</CODE>, if the given variable is not a variable specification.
     *
     * @param m a variable.
     * @return the corresponding variable specification, or <CODE>null</CODE>, if the given variable
     *         has no syntactical representation.
     */
    VariableSpecification getVariableSpecification(Variable v);

    /**
     * Returns this list of statements that will possibly be executed after the specified statement.
     * This method defines the edges of a control flow graph and obeys the Java compile-time
     * definitions for reachability. The graph is not transitive: The last statement of a loop will
     * return the loop as successor only, and the loop may have a successor that actually leaves the
     * loop. Statement that can leave the top level statement block will report
     * {@link #METHOD_EXIT}as a successor.
     *
     * @param s a statement.
     * @return a list of succeeding statements.
     * @since 0.71
     */
    List<Statement> getSucceedingStatements(Statement s);

    /**
     * Adds a progress listener for the model update process.
     *
     * @since 0.72
     */
    void addProgressListener(ProgressListener l);

    /**
     * Removes a progress listener for the model update process.
     *
     * @since 0.72
     */
    void removeProgressListener(ProgressListener l);


    /**
     * Returns the (annotation) type of the given annotation use.
     *
     * @param au an annotation use
     * @return the type of the referenced annotation type
     */
    Type getAnnotationType(AnnotationUseSpecification au);

}
