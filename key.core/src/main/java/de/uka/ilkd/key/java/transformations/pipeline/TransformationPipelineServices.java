/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.loader.JavaParserFactory;
import de.uka.ilkd.key.java.transformations.ConstantExpressionEvaluator;
import de.uka.ilkd.key.java.transformations.EvaluationException;
import de.uka.ilkd.key.speclang.PositionedString;

import org.key_project.util.collection.ImmutableList;

import com.github.javaparser.JavaParser;
import com.github.javaparser.Position;
import com.github.javaparser.ast.CompilationUnit;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.Node;
import com.github.javaparser.ast.NodeList;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.stmt.ExpressionStmt;
import com.github.javaparser.ast.stmt.Statement;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.VoidVisitorAdapter;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import org.checkerframework.checker.nullness.qual.MonotonicNonNull;
import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (11/2/21)
 */
@NullMarked
public class TransformationPipelineServices {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(TransformationPipelineServices.class);

    private final TransformerCache cache;

    private final JavaParserFactory javaParserFactory;

    private List<PositionedString> warnings = new ArrayList<>(8);

    public TransformationPipelineServices(JavaParserFactory javaParserFactory,
            TransformerCache cache) {
        this.cache = cache;
        this.javaParserFactory = javaParserFactory;
    }

    public void addWarning(PositionedString warning) {
        warnings.add(warning);
    }

    public void addWarnings(ImmutableList<PositionedString> w) {
        warnings.addAll(w.toList());
    }

    public void addWarnings(List<PositionedString> warnings) {
        this.warnings.addAll(warnings);
    }


    public TransformerCache getCache() {
        return cache;
    }

    public ConstantExpressionEvaluator getConstantEvaluator() {
        return new ConstantExpressionEvaluator();
    }

    public String getId(TypeDeclaration<?> td) {
        return td.getNameAsString();
    }

    /**
     * returns the default value of the given type
     * according to JLS Sect. 4.5.5
     *
     * @return the default value of the given type
     *         according to JLS Sect. 4.5.5
     */
    public Expression getDefaultValue(Type type) {
        if (type instanceof ReferenceType) {
            return new NullLiteralExpr();
        } else if (type instanceof PrimitiveType ptype) {
            switch (ptype.getType()) {
                case BOOLEAN:
                    return new BooleanLiteralExpr(false);
                case BYTE:
                case SHORT:
                case INT:
                    return new IntegerLiteralExpr("0");
                case LONG:
                    return new LongLiteralExpr("0");

                case CHAR:
                    return new CharLiteralExpr((char) 0);
                case FLOAT:
                case DOUBLE:
            }
        }
        LOGGER.error("makeImplicitMembersExplicit: unknown primitive type: {}", type);
        return null;
    }

    public ClassOrInterfaceType getType(String... names) {
        ClassOrInterfaceType type = null;
        for (String name : names) {
            type = new ClassOrInterfaceType(type, name);
        }
        return type;
    }

    public Name getName(String... names) {
        Name type = null;
        for (String name : names) {
            type = new Name(type, name);
        }
        return type;
    }

    /**
     * returns true if the given FieldDeclaration denotes a constant
     * field. A constant field is declared as final and static and
     * initialised with a time constant, which is not prepared or
     * initialised here. ATTENTION: this is a derivation from the JLS
     * but the obtained behaviour is equivalent as we only consider
     * completely compiled programs and not partial compilations. The
     * reason for preparation and initialisation of comnpile time
     * constant fields is due to binary compatibility reasons.
     */
    private boolean isConstant(Expression expr) {
        ConstantExpressionEvaluator ce = getConstantEvaluator();
        try {
            return ce.isCompileTimeConstant(expr);
        } catch (EvaluationException e) {
            LOGGER.error("Evaluation of {} resulted in exception", expr);
            return false;
        }
    }

    public boolean isConstant(Optional<Expression> initializer) {
        return initializer.map(this::isConstant).orElse(false);
    }

    public ClassOrInterfaceType getType(TypeDeclaration<?> decl) {
        return new ClassOrInterfaceType(null, decl.getName(), null);
    }

    public @Nullable Type getType(ResolvedType type) {
        if (type.isArray()) {
            // TODO weigl type.arrayLevel()
            return new ArrayType(getType(type.asArrayType().getComponentType()));
        }

        if (type.isReferenceType()) {
            return getType(type.asReferenceType().getQualifiedName().split("[.]"));
        }

        if (type.isPrimitive()) {
            return new PrimitiveType(PrimitiveType.Primitive.valueOf(type.asPrimitive().name()));
        }

        return null;
    }

    public List<SymbolReference<? extends ResolvedValueDeclaration>> getUsages(
            ResolvedValueDeclaration v, Node node) {
        // TODO
        return Collections.emptyList();
    }

    /// The list of statements is the smallest list that contains a copy
    /// assignment for each instance field initializer of class cd,
    /// e.g. ` i = 0; ` for ` public int i = 0; ` or
    /// a reference to the private method
    /// `<objectInitializer>_i_ refering to the i-th object
    /// initializer of cd. These private declared methods are created on
    /// the fly. Example for
    /// ```
    /// class C {
    /// int i = 0;
    /// {
    /// int j = 3;
    /// i = j + 5;
    /// }
    /// public C () {} ...
    /// }
    /// ```
    /// the following list of size two is returned
    /// ```
    /// [ i = 0;, &lt;objectInitializer&gt;0(); ]
    /// ```
    /// where `
    /// ```
    /// private &lt;objectInitializer&gt;0() {
    /// int j = 3;
    /// i = j + 5;
    /// }
    /// ```
    /// @param cd the TypeDeclaration of which the initializers have to be collected
    /// @return the list of copy assignments and method references realizing the initializers.`
    public NodeList<Statement> getInitializers(ClassOrInterfaceDeclaration cd) {
        NodeList<Statement> result = new NodeList<>();
        int objectInitializerCount = 0;
        for (BodyDeclaration<?> member : cd.getMembers().toArray(new BodyDeclaration[0])) {
            if (member instanceof InitializerDeclaration init &&
                    !init.isStatic()) {
                String name =
                    PipelineConstants.OBJECT_INITIALIZER_IDENTIFIER + objectInitializerCount;
                var initializerMethod = cd.addMethod(name, Modifier.DefaultKeyword.PRIVATE);
                initializerMethod.setBody(init.getBody().clone());
                initializerMethod.setParentNode(cd);
                result.add(new ExpressionStmt(new MethodCallExpr(name)));
                objectInitializerCount += 1;
            } else if (member instanceof FieldDeclaration field &&
                    !field.isStatic()) {
                for (VariableDeclarator variable : field.getVariables()) {
                    if (variable.getInitializer().isPresent()) {
                        Expression fieldInit = variable.getInitializer().get();
                        final var access = new FieldAccessExpr(
                            new ThisExpr(), new NodeList<>(), variable.getName());
                        var fieldCopy =
                            new AssignExpr(access, fieldInit.clone(), AssignExpr.Operator.ASSIGN);
                        result.add(new ExpressionStmt(fieldCopy));
                    }
                }
            }
        }

        return result;
    }

    public static <N extends Node> NodeList<N> cloneList(NodeList<N> list) {
        if (list == null) {
            return null;
        }
        var seq = list.stream()
                .map(Node::clone)
                .map(it -> (N) it)
                .collect(Collectors.toList());
        return new NodeList<>(seq);
    }

    public Expression getDefaultValue(ResolvedType type) {
        if (type.isPrimitive()) {
            var p = type.asPrimitive();
            if (p.isBoolean()) {
                return new BooleanLiteralExpr(false);
            }

            final var name = p.name();
            return switch (name.toLowerCase()) {
                case "int", "byte", "short" -> new IntegerLiteralExpr("0");
                case "char" -> new CharLiteralExpr("0");
                case "float", "double" -> new DoubleLiteralExpr("0.0");
                default ->
                    throw new IllegalStateException("Unexpected value: " + name.toLowerCase());
            };
        }

        if (type.isReferenceType()
                || type.isNull()
                || type.isArray()) {
            return new NullLiteralExpr();
        }

        if (type.isVoid()) {
            throw new RuntimeException();
        }

        return null;
    }

    public JavaParser getParser() {
        return javaParserFactory.createJavaParser();
    }


    /**
     * Cache of important data. This is done mainly for performance reasons.
     * It contains the following info:
     * - list of comp. units
     * - their class declarations
     * - a mapping from local classes to their needed final variables.
     * <p>
     * Objects are created upon the first request.
     *
     * @author MU
     */
    public static class TransformerCache {
        private final NodeList<CompilationUnit> cUnits = new NodeList<>();
        private Set<TypeDeclaration<?>> classDeclarations;

        public TransformerCache(List<CompilationUnit> cUnits) {
            this.cUnits.addAll(cUnits);
        }

        public Set<TypeDeclaration<?>> typeDeclarations() {
            if (classDeclarations == null) {
                init();
            }
            return classDeclarations;
        }

        private void init() {
            class FindTypes extends VoidVisitorAdapter<Void> {
                @Override
                public void visit(EnumDeclaration n, Void arg) {
                    classDeclarations.add(n);
                    super.visit(n, arg);
                }

                @Override
                public void visit(ClassOrInterfaceDeclaration n, Void arg) {
                    classDeclarations.add(n);
                    super.visit(n, arg);
                }

                @Override
                public void visit(RecordDeclaration n, Void arg) {
                    classDeclarations.add(n);
                    super.visit(n, arg);
                }

                @Override
                public void visit(AnnotationDeclaration n, Void arg) {
                    classDeclarations.add(n);
                    super.visit(n, arg);
                }
            }
            cUnits.accept(new FindTypes(), null);
        }

        public Set<ClassOrInterfaceDeclaration> classDeclarations() {
            return typeDeclarations().stream()
                    .filter(BodyDeclaration::isClassOrInterfaceDeclaration)
                    .map(it -> (ClassOrInterfaceDeclaration) it)
                    .collect(Collectors.toSet());
        }

        public Set<EnumDeclaration> enumDeclarations() {
            return typeDeclarations().stream()
                    .filter(BodyDeclaration::isEnumDeclaration)
                    .map(it -> (EnumDeclaration) it)
                    .collect(Collectors.toSet());
        }


        public Set<RecordDeclaration> recordDeclarations() {
            return typeDeclarations().stream()
                    .filter(BodyDeclaration::isRecordDeclaration)
                    .map(it -> (RecordDeclaration) it)
                    .collect(Collectors.toSet());
        }

        public List<ResolvedReferenceType> getAllSupertypes(TypeDeclaration<?> td) {
            return td.resolve().getAncestors();
            /*
             * if (td.isEnumDeclaration()) {
             * return Collections.singletonList(getType("java", "lang", "Enum"));
             * }
             *
             * if (td.isRecordDeclaration()) {
             * return Collections.singletonList(getType("java", "lang", "Record"));
             * }
             *
             * if (td.isAnnotationDeclaration()) {
             * return Collections.emptyList();
             * }
             *
             * ClassOrInterfaceDeclaration cd = (ClassOrInterfaceDeclaration) td;
             * var a = cd.resolve();
             * return typeDeclaration2allSupertypes.get(td);
             */
        }

        public List<CompilationUnit> getUnits() {
            return cUnits;
        }

    }

    /// Gets local variables outside the anonymous class `n` that should be treated as final fields
    /// for said anonymous class.
    public @Nullable List<ResolvedValueDeclaration> getLocalVarsExternalToAnonClass(
            TypeDeclaration<?> n) {
        return CaptureVariableCollector.collect(n).get(n);
    }

    public List<ResolvedValueDeclaration> getLocalVarsExternalToAnonClass(LambdaExpr n) {
        return CaptureVariableCollector.collect(n).get(n);
    }

    private static final class CaptureVariableCollector {
        public static Map<Node, List<ResolvedValueDeclaration>> collect(Node root) {
            Map<Node, List<ResolvedValueDeclaration>> result = new HashMap<>();

            // Handle lambdas
            root.findAll(LambdaExpr.class).forEach(lambda -> {
                result.put(lambda, findCaptured(lambda));
            });

            // Handle anonymous classes
            root.findAll(ObjectCreationExpr.class).stream()
                    .filter(oce -> oce.getAnonymousClassBody().isPresent())
                    .forEach(anon -> {
                        result.put(anon, findCaptured(anon));
                    });

            return result;
        }

        private static List<ResolvedValueDeclaration> findCaptured(Node scopeNode) {
            Set<ResolvedValueDeclaration> captured = new HashSet<>();

            scopeNode.findAll(NameExpr.class).forEach(nameExpr -> {
                try {
                    ResolvedValueDeclaration resolved = nameExpr.resolve();

                    // Only local variables
                    if (resolved instanceof VariableDeclarator) {
                        resolved.toAst().ifPresent(declNode -> {
                            if (!isInside(scopeNode, declNode)) {
                                captured.add(resolved);
                            }
                        });
                    }

                } catch (Exception ignored) {
                }
            });

            return new ArrayList<>(captured);
        }

        private static boolean isInside(Node container, Node declaration) {
            return declaration.getRange().isPresent() &&
                    container.getRange().isPresent() &&
                    container.containsWithinRange(declaration);
        }
    }
}
