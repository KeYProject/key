/**
 * This package contains KeY's internal model of Java programs.
 *
 * <p>
 * The model is a hand-written, immutable abstract syntax tree (AST) that
 * represents the analyzed Java source code. Parsed sources are loaded by the
 * classes in the {@code loader} subpackage (e.g.
 * {@link de.uka.ilkd.key.java.loader.JavaParserFactory} and
 * {@link de.uka.ilkd.key.java.loader.JP2KeYConverter}) and normalized by the
 * transformation pipeline in the {@code transformations} subpackage
 * ({@link de.uka.ilkd.key.java.transformations.KeYJavaPipeline}).
 * </p>
 *
 * <h2>AST nodes</h2>
 * <p>
 * The AST node hierarchy lives in the {@code de.uka.ilkd.key.java.ast} package:
 * a {@link de.uka.ilkd.key.java.ast.CompilationUnit} represents a complete Java
 * source file, {@link de.uka.ilkd.key.java.ast.JavaProgramElement} is the common
 * superclass of all nodes, and nodes are classified into
 * {@link de.uka.ilkd.key.java.ast.NonTerminalProgramElement}s (which know their
 * AST children) and terminal elements. Statements are
 * {@link de.uka.ilkd.key.java.ast.Statement}s, expressions live in the
 * {@code expression} subpackage, declarations in the {@code declaration}
 * subpackage, references in the {@code reference} subpackage, and type
 * abstractions independent of the concrete syntax (such as
 * {@link de.uka.ilkd.key.java.ast.abstraction.KeYJavaType}) in the
 * {@code abstraction} subpackage.
 * </p>
 *
 * <h2>Creating and inspecting the model</h2>
 * <p>
 * {@link de.uka.ilkd.key.java.KeYJavaASTFactory} provides factory methods for
 * creating AST nodes; {@link de.uka.ilkd.key.java.JavaInfo} holds the type
 * model of the analyzed program (its members, method calls, and class
 * hierarchy); {@link de.uka.ilkd.key.java.TypeConverter} and
 * {@link de.uka.ilkd.key.java.JavaAstUtils} offer conversion and analysis
 * helpers. Visitors for traversing the AST are provided by the {@code visitor}
 * subpackage, notably {@link de.uka.ilkd.key.java.visitor.JavaASTVisitor} and
 * {@link de.uka.ilkd.key.java.visitor.JavaASTWalker}.
 * </p>
 *
 * <p>
 * Most types of the model are immutable; transformations create new nodes
 * rather than modifying existing ones in place.
 * </p>
 */
package de.uka.ilkd.key.java;
