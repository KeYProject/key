/**
 * This package contains classes that cover the Java programming language.
 * These classes are fundamental for syntactical transformations and deserve
 * a detailed overview.
 * <DL>
 * <DT>Source and Program Elements</DT>
 * <DD>
 * A {@link recoder.java.SourceElement} is a syntactical entity and not
 * necessary a {@link recoder.ModelElement}, such as a {@link recoder.java.Comment}.
 * Each {@link recoder.java.SourceElement} knows its
 * {@link recoder.ProgramFactory}, its indentation and how to
 * {@link recoder.java.SourceElement#deepClone} itself.
 * <p>
 * A {@link recoder.java.ProgramElement} is a {@link recoder.java.SourceElement}
 * and a {@link recoder.ModelElement}. It is aware of its parent in the syntax
 * tree, while a pure {@link recoder.java.SourceElement} is not considered as a
 * member of the AST even though it is represented in the sources.
 * <p>
 * {@link recoder.java.ProgramElement}s are further
 * classified into {@link recoder.java.TerminalProgramElement}s and
 * {@link recoder.java.NonTerminalProgramElement}s (this is another
 * <I>Composite</I> pattern). While {@link recoder.java.TerminalProgramElement}
 * is just a tag class, {@link recoder.java.NonTerminalProgramElement}s know
 * their AST children (while it is possible that they do not have any).
 * A complete source file occurs as a {@link recoder.java.CompilationUnit}.
 * <p>
 * {@link recoder.java.JavaSourceElement} and
 * {@link recoder.java.JavaProgramElement} are abstract classes defining
 * standard implementations that already know their
 * {@link recoder.java.JavaProgramFactory}.
 * </DD>
 * <p>
 * <DT>Validation</DT>
 * <DD>
 * Calling the {@link recoder.ModelElement#validate()} method of a
 * {@link recoder.ModelElement} will check its consistency similar to the
 * analysis a compiler does. In case of an inconsistency, a
 * {@link recoder.ModelException} is thrown. The
 * {@link recoder.ModelElement#validate()} method of a
 * {@link recoder.java.ProgramElement} will check its children if
 * necessary. Calling {@link recoder.ModelElement#validate()} for a
 * {@link recoder.java.CompilationUnit} will check the consistency of the
 * whole module.
 * <p>
 * A {@link recoder.java.NonTerminalProgramElement} defines a
 * {@link recoder.java.NonTerminalProgramElement#makeParentRoleValid()} method
 * that sets all parent links of the current children. Not that a
 * {@link recoder.java.SourceElement} automatically keeps track of any attached
 * {@link recoder.java.Comment}.
 * The method is automatically invoked by each constructor that creates a
 * concrete and valid program element. Since some constructors create
 * partially initialized nodes only, there is no need to make them valid at
 * that time.
 * </DD>
 * <p>
 * <DT>Expressions and Statements</DT>
 * <DD>
 * {@link recoder.java.Expression} and {@link recoder.java.Statement} are
 * self-explanatory. A {@link recoder.java.LoopInitializer} is a special
 * {@link recoder.java.Statement} valid as initializer of
 * {@link recoder.java.statement.For} loops.
 * {@link recoder.java.LoopInitializer} is subtyped by
 * {@link recoder.java.expression.ExpressionStatement} and
 * {@link recoder.java.declaration.LocalVariableDeclaration}).
 * <p>
 * Concrete classes and further abstractions are bundled in the
 * {@link recoder.java.expression} and {@link recoder.java.statement} packages.
 * </DD>
 * <p>
 * <DT>Syntax Tree Parents</DT>
 * <DD>
 * There are a couple of abstractions dealing with properties of being a
 * parent node, which is used for upwards traversals in the syntax tree.
 * <p>
 * These are {@link recoder.java.declaration.TypeDeclarationContainer},
 * {@link recoder.java.ExpressionContainer},
 * {@link recoder.java.StatementContainer},
 * {@link recoder.java.ParameterContainer},
 * {@link recoder.java.NamedProgramElement} and
 * {@link recoder.java.reference.TypeReferenceContainer}. A
 * An {@link recoder.java.ExpressionContainer} contains
 * {@link recoder.java.Expression}s, a
 * {@link recoder.java.StatementContainer} contains
 * {@link recoder.java.Statement}s, a
 * {@link recoder.java.ParameterContainer}
 * (either a {@link recoder.java.declaration.MethodDeclaration} or a
 * {@link recoder.java.statement.Catch} statement) contains
 * {@link recoder.java.declaration.ParameterDeclaration}s.
 * A {@link recoder.java.NamedProgramElement} is a subtype of
 * {@link recoder.NamedModelElement}.
 * A {@link recoder.java.reference.TypeReferenceContainer} contains one or
 * several names, but these are names of types that are referred to explicitely
 * by a {@link recoder.java.reference.TypeReference}.
 * </DD>
 * <p>
 * <DT>References</DT>
 * <DD>
 * A {@link recoder.java.Reference} is an explicite use of an entity. Most of
 * these {@link recoder.java.Reference}s are
 * {@link recoder.java.reference.NameReference}s
 * and as such {@link recoder.java.NamedProgramElement}s, e.g. the
 * {@link recoder.java.reference.TypeReference}.
 * Subtypes of {@link recoder.java.Reference}s are bundled in the
 * {@link recoder.java.reference} package.
 * </DD>
 * <p>
 * <DT>Modifiers and Declarations</DT>
 * <DD>
 * {@link recoder.java.declaration.Modifier}s are (exclusively) used in the
 * context of {@link recoder.java.Declaration}s.
 * {@link recoder.java.declaration.Modifier}s occur explictely, since they occur
 * as syntactical tokens that might be indented and commented.
 * {@link recoder.java.Declaration}s are either
 * declarations of types or other entities such as
 * {@link recoder.java.declaration.MemberDeclaration} or
 * {@link recoder.java.declaration.VariableDeclaration}. Concrete
 * {@link recoder.java.declaration.Modifier}s and
 * {@link recoder.java.Declaration}s are
 * bundled in the {@link recoder.java.declaration.modifier} and
 * {@link recoder.java.declaration} packages.
 * </DD>
 * <p>
 * <DT>Comments</DT>
 * <DD>
 * A {@link recoder.java.ProgramElement} can have a list of
 * {@link recoder.java.Comment}s attached.
 * <p>
 * While a pure {@link recoder.java.Comment} can extend to several lines, a
 * {@link recoder.java.SingleLineComment} may not contain linefeeds.
 * A {@link recoder.java.DocComment} is a special comment used for
 * documentation systems such as JavaDoc or DOC++.
 * </DD>
 * </DL>
 */
package recoder.java;
