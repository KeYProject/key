/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.transformations.pipeline;

import java.util.*;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.loader.JavaParserFactory;
import de.uka.ilkd.key.java.transformations.ConstantExpressionEvaluator;
import de.uka.ilkd.key.java.transformations.EvaluationException;

import com.github.javaparser.JavaParser;
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
import com.github.javaparser.resolution.declarations.ResolvedFieldDeclaration;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.SymbolReference;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import org.jspecify.annotations.NonNull;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

/**
 * @author Alexander Weigl
 * @version 1 (11/2/21)
 */
public class TransformationPipelineServices {
    private static final Logger LOGGER =
        LoggerFactory.getLogger(TransformationPipelineServices.class);

    @NonNull
    private final TransformerCache cache;

    @NonNull
    private final JavaParserFactory javaParserFactory;


    public TransformationPipelineServices(@NonNull JavaParserFactory javaParserFactory,
            @NonNull TransformerCache cache) {
        this.cache = cache;
        this.javaParserFactory = javaParserFactory;
    }

    @NonNull
    public TransformerCache getCache() {
        return cache;
    }

    public ConstantExpressionEvaluator getConstantEvaluator() {
        return new ConstantExpressionEvaluator();
    }


    /*
     * protected TypeDeclaration<?> containingClass(TypeDeclaration<?> td) {
     * Node container = td.getContainingReferenceType();
     * if (container == null) {
     * container = td.getParentNode().get();
     * }
     * while (!(container instanceof TypeDeclaration<?>)) {
     * container = container.getParentNode().get();
     * }
     * return (TypeDeclaration<?>) container;
     * }
     */


    public String getId(TypeDeclaration<?> td) {
        return td.getNameAsString();
    }

    protected MethodDeclaration containingMethod(TypeDeclaration<?> td) {
        Node container = td.getParentNode().get();
        while (container != null && !(container instanceof MethodDeclaration)) {
            container = container.getParentNode().get();
        }
        return (MethodDeclaration) container;
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
        } else if (type instanceof PrimitiveType) {
            PrimitiveType ptype = (PrimitiveType) type;
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

    public Type getType(Expression n) {
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
            e.printStackTrace();
            return false;
        }
    }

    public boolean isConstant(Optional<Expression> initializer) {
        return initializer.map(this::isConstant).orElse(false);
    }

    public ClassOrInterfaceType getType(TypeDeclaration<?> decl) {
        return new ClassOrInterfaceType(null, decl.getName(), null);
    }

    /*
     * public ResolvedTypeDeclaration getJavaLangObject() {
     * return javaService.getTypeSolver().getSolvedJavaLangObject();
     * }
     */

    public Type getType(ResolvedType type) {
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
            ResolvedFieldDeclaration v, Node node) {
        // TODO
        return Collections.emptyList();// ;resolver.solveSymbol(v.getName(), node);
    }

    /**
     * The list of statements is the smallest list that contains a copy
     * assignment for each instance field initializer of class cd,
     * e.g. <code> i = 0; </code> for <code> public int i = 0; </code> or
     * a reference to the private method
     * <code>&lt;objectInitializer&gt;<i>i</i> refering to the i-th object
     * initializer of cd. These private declared methods are created on
     * the fly. Example for
     * <code><pre>
     * class C {
     * int i = 0;
     * {
     * int j = 3;
     * i = j + 5;
     * }
     * <p>
     * public C () {} ...
     * }</pre>
     * </code> the following list of size two is returned
     * <code><pre>
     * [ i = 0;,  &lt;objectInitializer&gt;0(); ]
     * </pre></code>
     * where <code><pre>
     * private &lt;objectInitializer&gt;0() {
     * int j = 3;
     * i = j + 5;
     * }</pre>
     * </code>
     *
     * @param cd
     *        the TypeDeclaration<?> of which the initilizers have to
     *        be collected
     * @return the list of copy assignments and method references
     *         realising the initializers.
     */
    public NodeList<Statement> getInitializers(ClassOrInterfaceDeclaration cd) {
        NodeList<Statement> result = new NodeList<>();
        NodeList<MethodDeclaration> mdl = new NodeList<>();

        var initializers =
            cd.getMembers().stream()
                    .filter(BodyDeclaration::isInitializerDeclaration)
                    .map(it -> (InitializerDeclaration) it)
                    .filter(it -> !it.isStatic())
                    .toList();


        for (InitializerDeclaration initializer : initializers) {
            String name = PipelineConstants.OBJECT_INITIALIZER_IDENTIFIER + mdl.size();
            var initializerMethod = cd.addMethod(name, Modifier.Keyword.PRIVATE);
            initializerMethod.setBody(initializer.getBody().clone());
            mdl.add(initializerMethod);
            result.add(new ExpressionStmt(new MethodCallExpr(name)));
        }

        var memberFields =
            cd.getMembers().stream()
                    .filter(BodyDeclaration::isFieldDeclaration)
                    .map(it -> (FieldDeclaration) it)
                    .filter(it -> !it.isStatic())
                    .toList();

        for (FieldDeclaration field : memberFields) {
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
            default -> throw new IllegalStateException("Unexpected value: " + name.toLowerCase());
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
        // private HashMap<ReferenceType, List<Name>> localClass2FinalVar;
        // private HashMap<TypeDeclaration, List<ReferenceType>> typeDeclaration2allSupertypes;

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

    public Collection<ResolvedFieldDeclaration> getFinalVariables(TypeDeclaration<?> n) {
        var seq = new LinkedList<ResolvedFieldDeclaration>();
        while (n.isNestedType()) {
            n = (TypeDeclaration<?>) n.getParentNode().get();
            var fields = n.resolve().getAllNonStaticFields();
            seq.addAll(fields);
        }
        return seq;
    }

    public LinkedList<ResolvedFieldDeclaration> getFinalVariables(LambdaExpr n) {
        return new LinkedList<>();
    }
}
