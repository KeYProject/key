/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.java.loader;

import java.net.URI;
import java.util.*;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.KeYJPMapping;
import de.uka.ilkd.key.java.Position;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.*;
import de.uka.ilkd.key.java.ast.Statement;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.ast.ccatch.*;
import de.uka.ilkd.key.java.ast.declaration.*;
import de.uka.ilkd.key.java.ast.declaration.TypeDeclaration;
import de.uka.ilkd.key.java.ast.declaration.modifier.*;
import de.uka.ilkd.key.java.ast.expression.ArrayInitializer;
import de.uka.ilkd.key.java.ast.expression.Expression;
import de.uka.ilkd.key.java.ast.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.ast.expression.PassiveExpression;
import de.uka.ilkd.key.java.ast.expression.literal.*;
import de.uka.ilkd.key.java.ast.expression.operator.*;
import de.uka.ilkd.key.java.ast.expression.operator.adt.*;
import de.uka.ilkd.key.java.ast.reference.*;
import de.uka.ilkd.key.java.ast.statement.*;
import de.uka.ilkd.key.java.transformations.ConstantExpressionEvaluator;
import de.uka.ilkd.key.java.transformations.EvaluationException;
import de.uka.ilkd.key.java.transformations.pipeline.JMLCommentTransformer;
import de.uka.ilkd.key.java.transformations.pipeline.JMLTransformer;
import de.uka.ilkd.key.ldt.HeapLDT;
import de.uka.ilkd.key.ldt.JavaDLTheory;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.VariableNamer;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.rule.metaconstruct.*;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLAssertStatement;
import de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLMergePointDecl;

import org.key_project.logic.op.Function;
import org.key_project.logic.sort.Sort;
import org.key_project.util.collection.ImmutableArray;

import com.github.javaparser.ast.*;
import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.key.*;
import com.github.javaparser.ast.key.sv.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.nodeTypes.NodeWithModifiers;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.resolution.UnsolvedSymbolException;
import com.github.javaparser.resolution.declarations.ResolvedValueDeclaration;
import com.github.javaparser.resolution.model.typesystem.ReferenceTypeImpl;
import com.github.javaparser.resolution.types.ResolvedType;
import com.github.javaparser.resolution.types.ResolvedVoidType;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserFieldDeclaration;
import com.github.javaparser.symbolsolver.javaparsermodel.declarations.JavaParserVariableDeclaration;
import org.jspecify.annotations.NonNull;
import org.jspecify.annotations.Nullable;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static java.lang.String.format;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public record JP2KeYConverter(Services services,KeYJPMapping mapping,@NonNull Namespace<SchemaVariable>schemaVariables,JP2KeYTypeConverter typeConverter){

public de.uka.ilkd.key.java.ast.CompilationUnit processCompilationUnit(com.github.javaparser.ast.CompilationUnit cu){return(de.uka.ilkd.key.java.ast.CompilationUnit)process(cu);}

public Object process(Node block){return block.accept(new JP2KeYVisitor(services,mapping,typeConverter,schemaVariables),null);}}


class JP2KeYVisitor extends GenericVisitorAdapter<Object, Void> {
    private static final Logger LOGGER = LoggerFactory.getLogger(JP2KeYConverter.class);
    private final Services services;
    private final KeYJPMapping mapping;
    private final JP2KeYTypeConverter typeConverter;
    @NonNull
    private final Namespace<SchemaVariable> schemaVariableNamespace;
    private final ConstantExpressionEvaluator evaluator;
    /**
     * Hashmap from variable spec to
     * <code>ProgramVariable</code>; this is necessary to avoid cycles when converting initializers.
     * Access to this map is performed via the method
     * <code>getProgramVariableForFieldSpecification</code>
     */
    private final Map<FullVariableDeclarator, ProgramVariable> fieldSpecificationMapping =
        new LinkedHashMap<>();

    JP2KeYVisitor(@NonNull Services services,
            @NonNull KeYJPMapping mapping, @NonNull JP2KeYTypeConverter typeConverter,
            @NonNull Namespace<SchemaVariable> schemaVariables) {
        this.services = services;
        this.mapping = mapping;
        this.typeConverter = typeConverter;
        schemaVariableNamespace = schemaVariables;
        this.evaluator = new ConstantExpressionEvaluator();
    }

    private <T> T reportError(Node n, String message) {
        JavaBuildingIssue problem = new JavaBuildingIssue(message, n);
        throw new JavaBuildingExceptions(Collections.singletonList(problem));
    }

    private <T> T reportUnsupportedElement(Node n) {
        return reportError(n, "Unsupported element detected given by Java Parser: "
            + n.getMetaModel().getTypeName() + ". Please extend the KeY-Java-Hierarchy");
    }

    @NonNull
    private TypeReference requireTypeReference(Type type) {
        return accept(type);
    }

    private <O extends ProgramElement> O addToMapping(Node value, O o) {
        mapping.put(value, o);
        return o;
    }

    private static ProgramElementName createProgramElementName(SimpleName n) {
        if (n.asString().startsWith("#")) {
            throw new IllegalArgumentException(
                "Creating a program element name from a string that identifies a schema variable");
        }
        var c = createComments(n);
        return new ProgramElementName(n.asString(), c.toArray(Comment[]::new));
    }

    @Override
    public Object visit(ArrayAccessExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Expression expr = accept(n.getIndex());
        Expression prefix = accept(n.getName());
        // TODO weigl how to express (new int[0])[0] in Java-KeY-AST?
        return new ArrayReference(pi, c, (ReferencePrefix) prefix, new ImmutableArray<>(expr));
    }

    @Override
    public Object visit(ArrayCreationExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        TypeReference type = accept(n.getElementType());
        // TODO javaparser how should int[5][4][][] be encoded in the key ast?
        ArrayInitializer ai;
        ImmutableArray<Expression> children;
        if (n.getInitializer().isPresent()) {
            ai = visitArrayInitializerExpr(n.getInitializer().get(), type.getKeYJavaType());
            children = null;
        } else {
            ai = null;
            children = map(n.getLevels());
        }

        int dimensions = n.getLevels().size();
        var rtype = n.calculateResolvedType();
        return new NewArray(pi, c, children, type, getKeYJavaType(rtype), dimensions, ai);
    }

    private ArrayInitializer visitArrayInitializerExpr(ArrayInitializerExpr n, KeYJavaType type) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        var list = new ArrayList<Expression>(n.getValues().size());
        for (var node : n.getValues()) {
            Expression expr;
            if (node instanceof ArrayInitializerExpr) {
                var array = ((de.uka.ilkd.key.java.ast.abstraction.ArrayType) type.getJavaType());
                expr = visitArrayInitializerExpr((ArrayInitializerExpr) node,
                    array.getBaseType().getKeYJavaType());
            } else {
                expr = accept(node);
            }
            list.add(expr);
        }
        var children = new ImmutableArray<>(list);
        return new ArrayInitializer(pi, c, children, type);
    }

    @Override
    public Object visit(AssertStmt n, Void arg) {
        Expression cond = accept(n.getCheck());
        Expression message = accepto(n.getMessage());
        return new Assert(cond, message, createPositionInfo(n));
    }

    @Override
    public Object visit(AssignExpr n, Void arg) {
        Expression target = accept(n.getTarget());
        Expression expr = accept(n.getValue());
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return switch (n.getOperator()) {
        case ASSIGN -> new CopyAssignment(pi, c, target, expr);
        case PLUS -> new PlusAssignment(pi, c, target, expr);
        case MINUS -> new MinusAssignment(pi, c, target, expr);
        case MULTIPLY -> new TimesAssignment(pi, c, target, expr);
        case DIVIDE -> new DivideAssignment(pi, c, target, expr);
        case BINARY_AND -> new BinaryAndAssignment(pi, c, target, expr);
        case BINARY_OR -> new BinaryOrAssignment(pi, c, target, expr);
        case XOR -> new BinaryXOrAssignment(pi, c, target, expr);
        case REMAINDER -> new ModuloAssignment(pi, c, target, expr);
        case LEFT_SHIFT -> new ShiftLeftAssignment(pi, c, target, expr);
        case SIGNED_RIGHT_SHIFT -> new ShiftRightAssignment(pi, c, target, expr);
        case UNSIGNED_RIGHT_SHIFT -> new UnsignedShiftRightAssignment(pi, c, target, expr);
        };
    }

    @Override
    public Object visit(BinaryExpr n, Void arg) {
        var lhs = (Expression) n.getLeft().accept(this, arg);
        var rhs = (Expression) n.getRight().accept(this, arg);
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return switch (n.getOperator()) {
        case OR -> new LogicalOr(pi, c, lhs, rhs);
        case AND -> new LogicalAnd(pi, c, lhs, rhs);
        case BINARY_OR -> new BinaryOr(pi, c, lhs, rhs);
        case BINARY_AND -> new BinaryAnd(pi, c, lhs, rhs);
        case XOR -> new BinaryXOr(pi, c, lhs, rhs);
        case EQUALS -> new Equals(pi, c, lhs, rhs);
        case NOT_EQUALS -> new NotEquals(pi, c, lhs, rhs);
        case LESS -> new LessThan(pi, c, lhs, rhs);
        case GREATER -> new GreaterThan(pi, c, lhs, rhs);
        case LESS_EQUALS -> new LessOrEquals(pi, c, lhs, rhs);
        case GREATER_EQUALS -> new GreaterOrEquals(pi, c, lhs, rhs);
        case LEFT_SHIFT -> new ShiftLeft(pi, c, lhs, rhs);
        case SIGNED_RIGHT_SHIFT -> new ShiftRight(pi, c, lhs, rhs);
        case UNSIGNED_RIGHT_SHIFT -> new UnsignedShiftRight(pi, c, lhs, rhs);
        case PLUS -> new Plus(pi, c, lhs, rhs);
        case MINUS -> new Minus(pi, c, lhs, rhs);
        case MULTIPLY -> new Times(pi, c, lhs, rhs);
        case DIVIDE -> new Divide(pi, c, lhs, rhs);
        case REMAINDER -> new Modulo(pi, c, lhs, rhs);
        };
    }

    @Override
    public Object visit(BlockStmt n, Void arg) {
        ImmutableArray<de.uka.ilkd.key.java.ast.Statement> body = map(n.getStatements());
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new StatementBlock(pi, c, body);
    }

    @Override
    public Object visit(BooleanLiteralExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new BooleanLiteral(pi, c, n.getValue());
    }

    @Override
    public Object visit(BreakStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        var name = simpleNameToLabel(n.getLabel());
        return new Break(pi, c, name);
    }

    @Override
    public Object visit(CastExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        TypeReference type = requireTypeReference(n.getType());
        return new TypeCast(pi, c, accept(n.getExpression()), type);
    }

    @Override
    public Object visit(CatchClause n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ParameterDeclaration param = accept(n.getParameter());
        return new Catch(pi, c, param, accept(n.getBody()));
    }

    @Override
    public Object visit(CharLiteralExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new CharLiteral(pi, c, n.getValue().charAt(0));
    }

    @Override
    public Object visit(ClassOrInterfaceDeclaration n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ProgramElementName name = createProgramElementName(n.getName());
        ProgramElementName fullName = new ProgramElementName(n.getFullyQualifiedName().get());
        boolean isLibrary = mapping.isParsingLibraries();
        ImmutableArray<de.uka.ilkd.key.java.ast.declaration.Modifier> modArray =
            map(n.getModifiers());
        ImmutableArray<MemberDeclaration> members = map(n.getMembers());
        boolean parentIsInterface = false;

        ImmutableArray<TypeReference> e = map(n.getExtendedTypes());
        ImmutableArray<TypeReference> i = map(n.getImplementedTypes());
        Extends extending = new Extends(e);
        Implements implementing = new Implements(i);

        var kjt = getKeYJavaType(new ReferenceTypeImpl(n.resolve()));

        TypeDeclaration td;
        if (n.isInterface()) {
            td = new InterfaceDeclaration(
                pi, c, modArray, name, fullName, members,
                parentIsInterface, isLibrary, extending);
        } else {
            td = new ClassDeclaration(pi, c, modArray, name, fullName, members, parentIsInterface,
                isLibrary, extending, implementing, n.isInnerClass(), n.isLocalClassDeclaration(),
                false);
        }
        kjt.setJavaType(td);
        return addToMapping(n, td);
    }

    @NonNull
    private <T> T accept(@NonNull Node check) {
        // noinspection unchecked
        return Objects.requireNonNull((T) check.accept(this, null));
    }

    private boolean parentIsInterface(@NonNull Node n) {
        if (n.getParentNode().isPresent()) {
            var parent = n.getParentNode().get();
            if (parent instanceof ClassOrInterfaceDeclaration) {
                return ((ClassOrInterfaceDeclaration) parent).isInterface();
            }
        }
        return false;
    }

    @NonNull
    private static PositionInfo createPositionInfo(Node node) {
        if (node.getRange().isEmpty()) {
            return PositionInfo.UNDEFINED;
        }
        var r = node.getRange().get();

        URI uri = node.findCompilationUnit()
                .flatMap(com.github.javaparser.ast.CompilationUnit::getStorage)
                .map(it -> it.getPath().toUri()).orElse(null);
        Position startPos = Position.fromJPPosition(r.begin);
        Position endPos = Position.fromJPPosition(r.end);
        return new PositionInfo(startPos, endPos, uri);
    }

    @Override
    public Object visit(ClassOrInterfaceType n, Void arg) {
        if (n.getTypeArguments().isPresent()) {
            return reportError(n, "Type arguments found.");
        }

        final var name = n.getNameAsString();
        if (name.startsWith("\\")) {
            JavaInfo ji = services.getJavaInfo();
            var type = ji.getPrimitiveKeYJavaType(name);
            if (type == null) {
                return reportError(n, "Unresolved KeY type");
            }
            return new TypeRef(type);
        }
        return getKeYJavaType(n);
    }

    @Override
    public Object visit(com.github.javaparser.ast.CompilationUnit n, Void arg) {
        return new de.uka.ilkd.key.java.ast.CompilationUnit(
            createPositionInfo(n), createComments(n),
            accepto(n.getPackageDeclaration()),
            map(n.getImports()),
            map(n.getTypes()));
    }

    private static List<Comment> createComments(Node n) {
        var comments = new ArrayList<Comment>();
        if (n.containsData(JMLCommentTransformer.BEFORE_COMMENTS)) {
            comments.addAll(n.getData(JMLCommentTransformer.BEFORE_COMMENTS).stream()
                    .map(c -> new Comment(c.asString(), createPositionInfo(c))).toList());
        }
        comments.addAll(n.getAssociatedSpecificationComments()
                .map(l -> l.stream().map(c -> new Comment(c.asString(), createPositionInfo(c)))
                        .toList())
                .orElse(Collections.emptyList()));
        return comments;
    }

    @SuppressWarnings("unchecked")
    private <T> ImmutableArray<T> map(NodeList<? extends Visitable> nodes) {
        var list = new ArrayList<T>(nodes.size());
        for (Node node : nodes) {
            var res = node.accept(this, null);
            list.add((T) Objects.requireNonNull(res));
        }
        return new ImmutableArray<>(list);
    }

    @SuppressWarnings("unchecked")
    private <T> ImmutableArray<T> flatMap(NodeList<? extends Visitable> nodes) {
        var seq = nodes.stream()
                .flatMap(it -> ((List<T>) Objects.requireNonNull(it.accept(this, null))).stream())
                .collect(Collectors.toList());
        return new ImmutableArray<>(seq);
    }

    @Nullable
    private <R> R accepto(Optional<? extends Node> node) {
        return node.<R>map(this::accept).orElse(null);
    }

    @Override
    public Object visit(ConditionalExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new Conditional(pi, c,
            accept(n.getCondition()),
            accept(n.getThenExpr()),
            accept(n.getElseExpr()));
    }

    @Override
    public Object visit(ConstructorDeclaration n, Void arg) {
        var isInInterface = parentIsInterface(n);
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ImmutableArray<TypeReference> exc = map(n.getThrownExceptions());
        Throws thr = exc.isEmpty() ? null : new Throws(null, null, exc);
        var cd = new de.uka.ilkd.key.java.ast.declaration.ConstructorDeclaration(pi, c,
            map(n.getModifiers()),
            null,
            null,
            createProgramElementName(n.getName()),
            map(n.getParameters()),
            thr,
            accept(n.getBody()), isInInterface);
        var containing = getContainingClass(n).resolve();
        final HeapLDT heapLDT = typeConverter.getTypeConverter().getHeapLDT();
        Sort heapSort = heapLDT == null ? JavaDLTheory.ANY : heapLDT.targetSort();
        final KeYJavaType containerKJT = getKeYJavaType(new ReferenceTypeImpl(containing));
        var method =
            new ProgramMethod(cd, containerKJT, KeYJavaType.VOID_TYPE, PositionInfo.UNDEFINED,
                heapSort, heapLDT == null ? 1 : heapLDT.getAllHeaps().size() - 1);
        return addToMapping(n, method);
    }

    @Override
    public Object visit(ContinueStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Label name = simpleNameToLabel(n.getLabel());
        return new Continue(pi, c, name);
    }

    private Label nameToLabel(Optional<Name> label) {
        return label.map(name -> {
            var str = name.asString();
            if (str.startsWith("#")) {
                return (Label) lookupSchemaVariable(str, name);
            }
            return new ProgramElementName(str);
        }).orElse(null);
    }

    @Nullable
    private Label simpleNameToLabel(Optional<SimpleName> label) {
        return label.map(l -> {
            if (l.asString().startsWith("#")) {
                return (Label) lookupSchemaVariable(l.asString(), l);
            }
            return createProgramElementName(l);
        }).orElse(null);
    }

    @Override
    public Object visit(DoStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        var guard = accept(n.getCondition());
        var body = accept(n.getBody());
        return new Do(pi, c, new Guard((Expression) guard),
            (Statement) body);
    }

    @Override
    public Object visit(DoubleLiteralExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new DoubleLiteral(pi, c, n.getValue());
    }

    @Override
    public Object visit(EmptyStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        if (n.containsData(JMLTransformer.KEY_CONSTRUCT)) {
            var construct = n.getData(JMLTransformer.KEY_CONSTRUCT);
            if (construct instanceof TextualJMLAssertStatement) {
                var a = (TextualJMLAssertStatement) construct;
                return new JmlAssert(a.getKind(), a.getContext(), pi, services);
            }
            if (construct instanceof TextualJMLMergePointDecl) {
                var a = (TextualJMLMergePointDecl) construct;
                var loc =
                    new LocationVariable(services.getVariableNamer().getTemporaryNameProposal("x"),
                        services.getNamespaces().sorts().lookup("boolean"));
                return new MergePointStatement(pi, c, a, loc);
            }
            LOGGER.warn(n.getRange() + " Ignoring statement " + construct.getClass());
        }
        return new EmptyStatement(pi, c);
    }

    @Override
    public Object visit(EnclosedExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        var expr = accept(n.getInner());
        return new ParenthesizedExpression(pi, c, (Expression) expr);
    }


    @Override
    public Object visit(ExplicitConstructorInvocationStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ImmutableArray<Expression> args = map(n.getArguments());
        return new SuperConstructorReference(args, pi, c);
    }

    @Override
    public Object visit(ExpressionStmt n, Void arg) {
        return accept(n.getExpression());
    }

    private static FieldSpecification findArrayLength(ArrayDeclaration type) {
        for (MemberDeclaration member : type.getMembers()) {
            if (!(member instanceof de.uka.ilkd.key.java.ast.declaration.FieldDeclaration field)) {
                continue;
            }
            for (FieldSpecification spec : field.getFieldSpecifications()) {
                if (Objects.equals(spec.getName(), "length")) {
                    return spec;
                }
            }
        }
        throw new IllegalStateException("array type without length field");
    }

    @Override
    public Object visit(FieldAccessExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        if (n.getNameAsString().startsWith("#")) {
            var scope = (ReferencePrefix) n.getScope().accept(this, arg);
            var name = (SchemaVariable) lookupSchemaVariable(n.getName());
            return new SchematicFieldReference(pi, c, name, scope);
        }

        // TODO weigl inspect this case
        try {
            ResolvedValueDeclaration target = n.resolve();
        } catch (UnsolvedSymbolException e) {
            ResolvedType type = n.calculateResolvedType();
            var keyType = getKeYJavaType(type);
            return new TypeRef(keyType);
        }

        /*
         * var ast = target.toAst().orElseThrow();
         * ProgramVariable pv = null;
         * if (target instanceof JavaParserFieldDeclaration) {
         * // Field declarations can have multiple variables
         * var decl = ((JavaParserFieldDeclaration) target).getVariableDeclarator();
         * var keyDecl = (VariableSpecification) mapping.nodeToKeY(decl);
         * pv = (ProgramVariable) keyDecl.getProgramVariable();
         * } else {
         * for (VariableSpecification variable : other.getVariables()) {
         * if (variable.getName() != null && JavaDLFieldNames.split(variable.getName()).name()
         * .equals(target.getName())) {
         * pv = (ProgramVariable) variable.getProgramVariable();
         * break;
         * }
         * }
         * }
         * if (pv == null) {
         * return reportUnsupportedElement(n);
         * }
         */

        var rtype = n.calculateResolvedType();
        var kjt = getKeYJavaType(rtype);
        var descriptor =
            "L" + n.getScope().toString().replace(".", "/") + "/" + n.getNameAsString() + ";";
        boolean notFullyQualifiedName = !rtype.toDescriptor().equals(descriptor);
        ProgramVariable variable =
            new LocationVariable(new ProgramElementName(n.getNameAsString()), kjt);
        if (notFullyQualifiedName) { // regular field access
            ReferencePrefix prefix = accept(n.getScope());
            return new FieldReference(pi, c, variable, prefix);
        } else {
            return new FieldReference(pi, c, variable, translatePackageReference(n.getScope()));
        }
    }

    @Override
    public Object visit(TypeExpr n, Void arg) {
        var rt = n.calculateResolvedType();
        var kjt = getKeYJavaType(rt);
        return new TypeRef(kjt);
    }


    private KeYJavaType getKeYJavaType(ResolvedType rtype) {
        return typeConverter.getKeYJavaType(rtype);
    }

    private ClassOrInterfaceDeclaration getContainingClass(Node node) {
        if (node instanceof ClassOrInterfaceDeclaration) {
            node = node.getParentNode().orElse(null);
        }
        while (node != null) {
            if (node instanceof ClassOrInterfaceDeclaration) {
                return (ClassOrInterfaceDeclaration) node;
            }
            node = node.getParentNode().orElse(null);
        }
        return null;
    }

    @Override
    public Object visit(FieldDeclaration n, Void arg) {
        var existing = mapping.nodeToKeY(n);
        if (existing != null) {
            return existing;
        }
        var pi = createPositionInfo(n);
        var c = createComments(n);
        var isInInterface = parentIsInterface(n);
        ImmutableArray<de.uka.ilkd.key.java.ast.declaration.Modifier> modArray =
            map(n.getModifiers());
        TypeReference type = requireTypeReference(n.getVariables().get(0).getType());
        var varsList = new ArrayList<FieldSpecification>(n.getVariables().size());
        for (VariableDeclarator v : n.getVariables()) {
            var isModel = n.hasModifier(Modifier.Keyword.MODEL);
            // This is really odd, some interfaces have represents clauses. Those should be abstract
            // classes...
            // Normal fields of interfaces are implicitly static...
            var isStatic = !isModel && n.isStatic();
            var decl = new FullVariableDeclarator(v, n.isFinal(), isStatic, isModel);
            final var fs = visitFieldSpecification(decl);
            varsList.add(fs);
            mapping.put(v, fs);
        }
        var fieldSpecs = new ImmutableArray<>(varsList);
        final var decl =
            new de.uka.ilkd.key.java.ast.declaration.FieldDeclaration(pi, c, modArray, type,
                isInInterface, fieldSpecs);
        return addToMapping(n, decl);
    }

    @Override
    public Object visit(ForEachStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        LocalVariableDeclaration decl = accept(n.getVariable());
        ILoopInit init = new LoopInit(new LoopInitializer[] { decl });
        Guard guard = new Guard(null, null, accept(n.getIterable()));
        return new EnhancedFor(pi, c, init, guard, accept(n.getBody()));
    }

    @Override
    public Object visit(ForStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ImmutableArray<LoopInitializer> inits = map(n.getInitialization());
        ImmutableArray<Expression> updates = map(n.getUpdate());
        Object guard = accepto(n.getCompare());

        IGuard forGuard;
        if (guard instanceof ProgramSV) {
            forGuard = (ProgramSV) guard;
        } else {
            forGuard = new Guard(pi, null, (Expression) guard);
        }

        ILoopInit forInit = null;
        if (inits.size() == 1 && inits.get(0) instanceof ProgramSV) {
            forInit = (ProgramSV) inits.get(0);
        } else if (!n.getInitialization().isEmpty()) {
            forInit = new LoopInit(inits);
        }

        IForUpdates forUpdates = null;
        if (updates.size() == 1 && updates.get(0) instanceof ProgramSV) {
            forUpdates = (ProgramSV) updates.get(0);
        } else if (!n.getUpdate().isEmpty()) {
            forUpdates = new ForUpdates(updates);
        }
        return new For(pi, c, forInit, forUpdates, forGuard, accept(n.getBody()));
    }

    @Override
    public Object visit(IfStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Statement t = accept(n.getThenStmt());
        Statement e = accepto(n.getElseStmt());
        return new If(pi, c, accept(n.getCondition()),
            new Then(t),
            e != null ? new Else(e) : null);
    }

    @Override
    public Object visit(InitializerDeclaration n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        StatementBlock body = accept(n.getBody());
        var mods =
            n.isStatic() ? new de.uka.ilkd.key.java.ast.declaration.Modifier[] { new Static() }
                    : new de.uka.ilkd.key.java.ast.declaration.Modifier[0];
        return new ClassInitializer(mods, body, pi, c);
    }

    @Override
    public Object visit(InstanceOfExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Expression lhs = accept(n.getExpression());
        var type = requireTypeReference(n.getType());
        return new Instanceof(pi, c, lhs, type);
    }

    @Override
    public Object visit(IntegerLiteralExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new IntLiteral(pi, c, n.getValue());
    }

    @Override
    public Object visit(LabeledStmt n, Void arg) {
        Label id;
        if (n.getLabel().asString().startsWith("#")) {
            id = (ProgramSV) lookupSchemaVariable(n.getLabel());
        } else {
            id = createProgramElementName(n.getLabel());
        }
        var stmt = accept(n.getStatement());
        return new LabeledStatement(id, (de.uka.ilkd.key.java.ast.Statement) stmt,
            createPositionInfo(n));
    }

    @Override
    public Object visit(LongLiteralExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new LongLiteral(pi, c, n.getValue());
    }

    @Override
    public Object visit(MethodCallExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        if (n.getNameAsString().startsWith("\\")) {
            return handleSpecialFunctionInvocation(n, n.getNameAsString(), n.getArguments());
        }

        MethodName name;
        if (n.getName().asString().startsWith("#")) {
            name = (MethodName) lookupSchemaVariable(n.getName().asString(), n.getName());
        } else {
            name = createProgramElementName(n.getName());
        }
        ReferencePrefix prefix = accepto(n.getScope());
        ImmutableArray<Expression> args = map(n.getArguments());
        return new MethodReference(pi, c, prefix, name, args);
    }

    @Override
    public Object visit(MethodDeclaration n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);

        ImmutableArray<TypeReference> t = map(n.getThrownExceptions());
        var thr = t.isEmpty() ? null : new Throws(null, null, t);
        var isInInterface = parentIsInterface(n);
        TypeReference returnType = requireTypeReference(n.getType());

        var md = new de.uka.ilkd.key.java.ast.declaration.MethodDeclaration(
            pi, c, map(n.getModifiers()),
            returnType,
            null,
            createProgramElementName(n.getName()),
            map(n.getParameters()),
            thr,
            accepto(n.getBody()),
            isInInterface);

        var containing = getContainingClass(n).resolve();
        final HeapLDT heapLDT = typeConverter.getTypeConverter().getHeapLDT();
        Sort heapSort = heapLDT == null ? JavaDLTheory.ANY : heapLDT.targetSort();
        final KeYJavaType containerType = getKeYJavaType(new ReferenceTypeImpl(containing));
        // may be null for a void method
        var method = new ProgramMethod(md, containerType, returnType.getKeYJavaType(), pi,
            heapSort, heapLDT == null ? 1 : heapLDT.getAllHeaps().size() - 1);
        return addToMapping(n, method);
    }

    @Override
    public Object visit(NameExpr n, Void arg) {
        if (n.getNameAsString().startsWith("#")) {
            return lookupSchemaVariable(n.getName());
        }

        ResolvedValueDeclaration target;
        try {
            target = n.resolve();
        } catch (UnsolvedSymbolException e) {
            ResolvedType type = n.calculateResolvedType();
            var keyType = getKeYJavaType(type);
            return new TypeRef(keyType);
        }
        if (target.toAst().isEmpty()) {
            return reportUnsupportedElement(n);
        }

        var ast = target.toAst().get();
        // Make sure the field is already converted
        var tmp = (VariableDeclaration) mapping.nodeToKeY(ast);
        VariableDeclaration other = tmp == null ? accept(ast) : tmp;
        var pi = createPositionInfo(n);
        var c = createComments(n);
        if (target instanceof JavaParserFieldDeclaration) {
            // Field declarations can have multiple variables
            var decl = ((JavaParserFieldDeclaration) target).getVariableDeclarator();
            var keyDecl = (VariableSpecification) Objects.requireNonNull(mapping.nodeToKeY(decl));
            var pv = (ProgramVariable) keyDecl.getProgramVariable();
            if (pv.isMember()) {
                // TODO javaparser prefix null? should we add default this?
                return new FieldReference(pi, c, pv, null);
            }
            // This seems to happen when we create a fake field in JavaService::createContext
            return pv;
        }
        if (target instanceof JavaParserVariableDeclaration) {
            // Variable declarations can have multiple variables
            var decl = ((JavaParserVariableDeclaration) target).getVariableDeclarator();
            var keyDecl = (VariableSpecification) Objects.requireNonNull(mapping.nodeToKeY(decl));
            return keyDecl.getProgramVariable();
        }
        if (other.getVariables().size() == 1) {
            return other.getVariables().get(0).getProgramVariable();
        }
        return reportUnsupportedElement(target.toAst().get());
    }

    @Override
    public Object visit(NormalAnnotationExpr n, Void arg) {
        // TODO
        return super.visit(n, arg);
    }

    @Override
    public Object visit(NullLiteralExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new NullLiteral(pi, c);
    }

    @Override
    public Object visit(ObjectCreationExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ImmutableArray<Expression> args = map(n.getArguments());
        TypeReference type = requireTypeReference(n.getType());

        ClassDeclaration decl = null;
        if (n.getAnonymousClassBody().isPresent()) {
            ImmutableArray<MemberDeclaration> bodies = map(n.getAnonymousClassBody().get());
            decl = new ClassDeclaration(pi, c, new ImmutableArray<>(), null, null,
                bodies, true, false, null, null,
                true, false, true);
        }
        return new New(pi, c, args, type, decl);
    }

    @Override
    public Object visit(PackageDeclaration n, Void arg) {
        if (n.getAnnotations().isNonEmpty()) {
            return reportUnsupportedElement(n);
        }

        mapping.registerPackageName(n.getName().asString());
        var ref = translatePackageReference(n.getName());
        return new PackageSpecification(ref);
    }

    private ReferencePrefix translatePackageReference(
            com.github.javaparser.ast.expr.Expression name) {
        if (name.isFieldAccessExpr()) {
            var fa = name.asFieldAccessExpr();
            var pen = createProgramElementName(fa.getName());
            var inner = translatePackageReference(fa.getScope());
            return new PackageReference(pen, inner);
        } else if (name.isNameExpr()) {
            var n = name.asNameExpr();
            var pen = createProgramElementName(n.getName());
            return new PackageReference(pen, null);
        }
        throw new IllegalArgumentException("Unexpected expression type: " + name.getClass());
    }

    @NonNull
    private PackageReference translatePackageReference(Name name) {
        // Translate recursively since PackageReference and Name are ordered differently
        var pen = new ProgramElementName(name.getIdentifier(),
            createComments(name).toArray(Comment[]::new));
        var inner = name.getQualifier().map(this::translatePackageReference).orElse(null);
        return new PackageReference(pen, inner);
    }

    private static ReferencePrefix convertScopeToReferencePrefix(ClassOrInterfaceType scope) {
        var name = scope.getName();
        var inner = scope.getScope().map(JP2KeYVisitor::convertScopeToReferencePrefix).orElse(null);
        return new PackageReference(createProgramElementName(name), inner);
    }

    @NonNull
    private Object getKeYJavaType(ClassOrInterfaceType type) {
        if (type.getName().asString().startsWith("#")) {
            return lookupSchemaVariable(type.asString(), type);
        }
        ReferencePrefix prefix =
            type.getScope().map(JP2KeYVisitor::convertScopeToReferencePrefix).orElse(null);
        var name = createProgramElementName(type.getName());
        var resolvedType = getKeYJavaType(type.resolve());
        return new TypeRef(name, 0, prefix, resolvedType);
    }

    private ParameterDeclaration visitNoMap(Parameter n) {
        ImmutableArray<de.uka.ilkd.key.java.ast.declaration.Modifier> modifiers =
            map(n.getModifiers());
        var va = n.isVarArgs();
        TypeReference type = accept(n.getType());
        var pi = createPositionInfo(n);
        var c = createComments(n);
        IProgramVariable pv;
        if (n.getName().toString().startsWith("#")) {
            pv = (IProgramVariable) lookupSchemaVariable(n.getName());
        } else {
            var name = VariableNamer.parseName(n.getName().asString());
            pv = new LocationVariable(name, type.getKeYJavaType(), n.isFinal());
        }
        var spec = new VariableSpecification(pi, c, null, pv, 0, type.getKeYJavaType());
        var isInInterface = parentIsInterface(n);
        return new ParameterDeclaration(new ImmutableArray<>(spec), pi, c, modifiers,
            type, isInInterface, va);
    }

    @Override
    public Object visit(Parameter n, Void arg) {
        var param = visitNoMap(n);
        return addToMapping(n, param);
    }

    @Override
    public TypeReference visit(PrimitiveType n, Void arg) {
        return new TypeRef(getKeYJavaType(n.resolve()));
    }

    @Override
    public Object visit(Name n, Void arg) {
        if (n.getIdentifier().startsWith("#")) {
            return lookupSchemaVariable(n.getIdentifier(), n);
        }

        // TODO javaparser Is this the correct translation for an arbitrary fqdn?
        return new LocationVariable(new ProgramElementName(n.getIdentifier()), (Sort) null);
    }

    @Override
    public Object visit(SimpleName n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(ArrayType n, Void arg) {
        return new TypeRef(getKeYJavaType(n.resolve()));
    }

    @Override
    public Object visit(ArrayCreationLevel n, Void arg) {
        return this.<Expression>accepto(n.getDimension());
    }

    @Override
    public Object visit(IntersectionType n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(UnionType n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(ReturnStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Expression expr = accepto(n.getExpression());
        return new Return(expr, pi, c);
    }

    @Override
    public Object visit(SingleMemberAnnotationExpr n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(StringLiteralExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new StringLiteral(pi, c, '"' + n.getValue() + '"');
    }

    @Override
    public Object visit(SuperExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        // TODO
        ReferencePrefix path = null;
        return new SuperReference(path, pi, c);
    }

    @Override
    public Object visit(SwitchEntry n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ImmutableArray<Statement> body = map(n.getStatements());
        if (n.getLabels().isEmpty()) {
            // Default branch
            return List.of(new Default(body, pi, c));
        } else {
            // TODO javaparser we currently multiply the branches
            var result = new ArrayList<Case>(n.getLabels().size());
            for (var label : n.getLabels()) {
                Expression expr = accept(label);
                result.add(new Case(expr, body, pi, c));
            }
            return result;
        }
    }

    @Override
    public Object visit(SwitchStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Expression expr = accept(n.getSelector());
        ImmutableArray<Branch> branches = flatMap(n.getEntries());
        return new Switch(pi, c, expr, branches);
    }

    @Override
    public Object visit(SynchronizedStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new SynchronizedBlock(pi, c, accept(n.getExpression()), accept(n.getBody()), null,
            0);
    }

    @Override
    public Object visit(ThisExpr n, Void arg) {
        // TODO
        ReferencePrefix prefix = null;
        return new ThisReference(createPositionInfo(n), createComments(n), prefix);
    }

    @Override
    public Object visit(ThrowStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Expression expr = accept(n.getExpression());
        return new Throw(expr, pi, c);
    }

    @Override
    public Object visit(TryStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        StatementBlock body = accept(n.getTryBlock());
        ImmutableArray<Branch> branches = map(n.getCatchClauses());
        if (n.getFinallyBlock().isPresent()) {
            StatementBlock block = accept(n.getFinallyBlock().get());
            var fin = new Finally(block);
            var list = branches.toList();
            list.add(fin);
            branches = new ImmutableArray<>(list);
        }
        return new Try(pi, c, body, branches, null, 0);
    }


    @Override
    public Object visit(UnaryExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        if (n.getOperator() == UnaryExpr.Operator.MINUS) {
            var expr = n.getExpression();
            if (expr instanceof IntegerLiteralExpr lit) {
                var num = lit.asNumber();
                if (num instanceof Long) {
                    if (-num.longValue() != (long) Integer.MIN_VALUE) {
                        return reportUnsupportedElement(n);
                    }
                    return new IntLiteral(pi, c, Integer.MIN_VALUE);
                }
                return new IntLiteral(pi, c, -num.intValue());
            }
            return new Negative(pi, c, accept(expr));
        }
        Expression child = accept(n.getExpression());
        return switch (n.getOperator()) {
        case PLUS -> new Positive(pi, c, child);
        case MINUS -> throw new IllegalStateException();
        case PREFIX_INCREMENT -> new PreIncrement(pi, c, child);
        case PREFIX_DECREMENT -> new PreDecrement(pi, c, child);
        case LOGICAL_COMPLEMENT -> new LogicalNot(pi, c, child);
        case BITWISE_COMPLEMENT -> new BinaryNot(pi, c, child);
        case POSTFIX_INCREMENT -> new PostIncrement(pi, c, child);
        case POSTFIX_DECREMENT -> new PostDecrement(pi, c, child);
        };
    }

    @Override
    public Object visit(UnknownType n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(VariableDeclarationExpr n, Void arg) {
        var existing = mapping.nodeToKeY(n);
        if (existing != null) {
            return existing;
        }
        TypeReference type = requireTypeReference(n.getVariable(0).getType());
        var varsList = new ArrayList<VariableSpecification>(n.getVariables().size());
        for (VariableDeclarator v : n.getVariables()) {
            varsList.add(visitVariableSpecification(type, v, n));
        }
        var vars = new ImmutableArray<>(varsList);
        ImmutableArray<de.uka.ilkd.key.java.ast.declaration.Modifier> modifiers =
            map(n.getModifiers());
        var pi = createPositionInfo(n);
        var c = createComments(n);
        var isInInterface = parentIsInterface(n);
        return addToMapping(n,
            new LocalVariableDeclaration(pi, c, modifiers, type, isInInterface, vars));
    }


    private VariableSpecification visitVariableSpecification(TypeReference type,
            VariableDeclarator v,
            NodeWithModifiers<?> modifiers) {
        var pi = createPositionInfo(v);
        var c = createComments(v);
        Expression init = accepto(v.getInitializer());
        IProgramVariable pv;
        KeYJavaType kjt = type.getKeYJavaType();
        if (v.getNameAsString().startsWith("#")) {
            pv = (IProgramVariable) lookupSchemaVariable(v.getNameAsString(), v);
        } else {
            var name = VariableNamer.parseName(v.getNameAsString());
            pv = new LocationVariable(name, kjt, modifiers.hasModifier(Modifier.Keyword.FINAL));
        }

        return addToMapping(v, new VariableSpecification(pi, c, init, pv, 0, kjt));
    }

    /**
     * @return a literal constant representing the value of <code>p_er</code>
     */
    private Literal getLiteralFor(LiteralExpr lit) {
        if (lit.isBooleanLiteralExpr()) {
            return BooleanLiteral.getBooleanLiteral(lit.asBooleanLiteralExpr().getValue());
        } else if (lit.isCharLiteralExpr()) {
            return new CharLiteral(lit.asCharLiteralExpr().getValue());
        } else if (lit.isDoubleLiteralExpr()) {
            // TODO javaparser there are only double or float literals in jp
            return new DoubleLiteral(lit.asDoubleLiteralExpr().getValue());
        } else if (lit.isIntegerLiteralExpr()) {
            // TODO javaparser there are only int literals in jp, not byte short int
            var value = lit.asIntegerLiteralExpr().getValue();
            // TODO weigl 1L is a javaparser int literal?
            if (value.endsWith("L") || value.endsWith("l")) {
                return new LongLiteral(value);
            } else {
                return new IntLiteral(value);
            }
        } else if (lit.isLongLiteralExpr()) {
            return new LongLiteral(lit.asLongLiteralExpr().getValue());
        } else if (lit.isNullLiteralExpr()) {
            return new NullLiteral();
        } else if (lit.isStringLiteralExpr()) {
            assert lit.asStringLiteralExpr().getValue() != null;
            return new StringLiteral(lit.asStringLiteralExpr().getValue());
        } else if (lit.isTextBlockLiteralExpr()) {
            return new StringLiteral(lit.asTextBlockLiteralExpr().getValue());
        } else {
            return reportUnsupportedElement(lit);
        }
    }

    /**
     * @return a literal constant representing the value of the initializer of
     *         <code>recoderVarSpec</code>, if the variable is a compile-time constant, and
     *         <code>null</code> otherwise
     */
    private Literal getCompileTimeConstantInitializer(FullVariableDeclarator spec) {
        // Necessary condition: the field is static and final
        if (!spec.isFinal || !spec.isStatic) {
            return null;
        }

        var init = spec.decl.getInitializer();

        if (init.isPresent()) {
            try {
                var expr = evaluator.evaluate(init.get());
                if (expr.isLiteralExpr()) {
                    return getLiteralFor(expr.asLiteralExpr());
                }
            } catch (EvaluationException ignored) {
            }
        }

        return null;
    }

    /**
     * this is needed by #convert(FieldSpecification).
     */
    private ProgramVariable getProgramVariableForFieldSpecification(FullVariableDeclarator decl) {
        ProgramVariable pv = fieldSpecificationMapping.get(decl);

        if (pv != null) {
            return pv;
        }
        var spec = decl.decl;
        var varSpec = mapping.nodeToKeY(spec);
        if (varSpec == null) {
            var t = spec.getType().resolve();
            var classNode = findContainingClass(spec).orElseThrow();
            var classType = new ReferenceTypeImpl(classNode.resolve());
            final ProgramElementName pen =
                new ProgramElementName(spec.getName().asString(),
                    classNode.getFullyQualifiedName().orElseThrow());

            final Literal compileTimeConstant = getCompileTimeConstantInitializer(decl);

            if (compileTimeConstant == null) {
                pv = new LocationVariable(pen, getKeYJavaType(t),
                    getKeYJavaType(classType), decl.isStatic, decl.isModel,
                    false, decl.isFinal);
            } else {
                pv = new ProgramConstant(pen, getKeYJavaType(t),
                    getKeYJavaType(classType), decl.isStatic,
                    compileTimeConstant);
            }
        } else {
            pv = (ProgramVariable) ((VariableSpecification) varSpec).getProgramVariable();
        }
        fieldSpecificationMapping.put(decl, pv);

        assert pv != null;
        return pv;
    }

    private static Optional<ClassOrInterfaceDeclaration> findContainingClass(Node node) {
        return findParent(node, n -> n instanceof ClassOrInterfaceDeclaration)
                .map(c -> (ClassOrInterfaceDeclaration) c);
    }

    private static Optional<Node> findParent(Node node, Predicate<Node> filter) {
        Optional<Node> n = Optional.of(node);
        while (n.isPresent() && !filter.test(n.get())) {
            n = n.get().getParentNode();
        }
        return n;
    }

    private FieldSpecification visitFieldSpecification(FullVariableDeclarator v) {
        var pi = createPositionInfo(v.decl);
        var c = createComments(v.decl);
        Expression init = accepto(v.decl.getInitializer());
        var type = getKeYJavaType(v.decl.getType().resolve());
        var pv = getProgramVariableForFieldSpecification(v);
        return new FieldSpecification(pi, c, init, pv, 0, type);
    }

    @Override
    public Object visit(VariableDeclarator n, Void arg) {
        // Only allowed inside VariableDeclarationExpr which is handled above
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(VoidType n, Void arg) {
        return new TypeRef(getKeYJavaType(ResolvedVoidType.INSTANCE));
    }

    @Override
    public Object visit(WhileStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Guard guard = new Guard((Expression) accept(n.getCondition()));
        Statement body = accept(n.getBody());
        return new While(pi, c, guard, body);
    }

    @Override
    public Object visit(ImportDeclaration n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);

        if (n.isStatic()) {
            return reportUnsupportedElement(n);
        }

        if (n.isAsterisk()) {
            // TODO javaparser Class.* works as well
            var ref = translatePackageReference(n.getName());
            return new Import(ref, pi, c);
        } else {
            TypeReference type = null; // TODO weigl
            return new Import(type, n.isAsterisk(), pi, c);
        }
    }

    @Override
    public Object visit(Modifier n, Void arg) {
        var pi=createPositionInfo(n);var c=createComments(n);var k=n.getKeyword();return switch(k){case PUBLIC->new Public(pi,c);case PROTECTED->new Protected(pi,c);case PRIVATE->new Private(pi,c);case ABSTRACT->new Abstract(pi,c);case STATIC->new Static(pi,c);case FINAL->new Final(pi,c);case TRANSIENT->new Transient(pi,c);case VOLATILE->new Volatile(pi,c);case SYNCHRONIZED->new Synchronized(pi,c);case NATIVE->new Native(pi,c);case STRICTFP->new StrictFp(pi,c);case GHOST->new Ghost(pi,c);case MODEL->new Model(pi,c);case TWO_STATE->new TwoState(pi,c);case NO_STATE->new NoState(pi,c);default->{reportUnsupportedElement(n);yield null;}};
    }


    // region ccatch
    @Override
    public Object visit(KeyCcatchBreak n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        CcatchNonstandardParameterDeclaration param;
        if (n.getLabel().isPresent()) {
            if (n.getLabel().get().asString().equals("*")) {
                param = new CcatchBreakWildcardParameterDeclaration(pi, c);
            } else {
                var label = nameToLabel(n.getLabel());
                param = new CcatchBreakLabelParameterDeclaration(pi, c, label);
            }
        } else {
            param = new CcatchBreakParameterDeclaration(pi, c);
        }
        StatementBlock block = accepto(n.getBlock());
        return new Ccatch(pi, c, null, param, block);
    }

    @Override
    public Object visit(KeyCcatchContinue n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        CcatchNonstandardParameterDeclaration param;
        if (n.getLabel().isPresent()) {
            if (n.getLabel().get().asString().equals("*")) {
                param = new CcatchContinueWildcardParameterDeclaration(pi, c);
            } else {
                var label = nameToLabel(n.getLabel());
                param = new CcatchContinueLabelParameterDeclaration(pi, c, label);
            }
        } else {
            param = new CcatchContinueParameterDeclaration(pi, c);
        }
        StatementBlock block = accepto(n.getBlock());
        return new Ccatch(pi, c, null, param, block);
    }

    @Override
    public Object visit(KeyCcatchParameter n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        // reportUnsupportedElement(n);
        TypeReference typeRef = (TypeReference) n.getParameter().get().getType().accept(this, arg);

        ProgramSV name = (ProgramSV) lookupSchemaVariable(n.getParameter().get().getName());
        VariableSpecification v = new VariableSpecification(name);
        ParameterDeclaration parameter = new ParameterDeclaration(
            new de.uka.ilkd.key.java.ast.declaration.Modifier[0],
            typeRef, v, false);

        StatementBlock body = n.getBlock().isEmpty()
                ? new StatementBlock()
                : (StatementBlock) n.getBlock().get().accept(this, arg);
        return new Ccatch(pi, c, parameter, null, body);
    }

    @Override
    public Object visit(KeyCcatchReturn n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        CcatchNonstandardParameterDeclaration param;
        if (n.getParameter().isPresent()) {
            ParameterDeclaration delegate = accept(n.getParameter().get());
            param = new CcatchReturnValParameterDeclaration(pi, c, delegate);
        } else {
            param = new CcatchReturnParameterDeclaration(pi, c);
        }
        StatementBlock block = accepto(n.getBlock());
        return new Ccatch(pi, c, null, param, block);
    }

    @Override
    public Object visit(KeyCatchAllStatement n, Void arg) {
        // TODO
        return reportUnsupportedElement(n);
    }
    // endregion

    @Override
    public Object visit(KeyEscapeExpression n, Void arg) {
        return handleSpecialFunctionInvocation(n, n.getCallee().asString(),
            n.getArguments().orElse(new NodeList<>()));
    }

    public Object handleSpecialFunctionInvocation(Node n, String name,
                                                  NodeList<com.github.javaparser.ast.expr.Expression> arguments) {
        var pi = createPositionInfo(n);
        var c = createComments(n);

        final var PREFIX = "\\dl_DEFAULT_VALUE_";
        final var DEFVALUE = "@defaultValue(";

        if (name.startsWith(PREFIX)) { // handle default value resolution
            String sortName = name.substring(PREFIX.length()).trim();
            Sort sort = services.getNamespaces().sorts().lookup(sortName);
            if (sort == null) {
                return reportError(n, format(
                        "Requested to find the default value of an unknown sort '%s'.", sortName));
            }

            var doc = sort.getDocumentation();

            if (doc == null) {
                return reportError(n,
                        format("Requested to find the default value for the sort '%s', " +
                                        "which does not have a documentary comment. The sort is defined at %s. ",
                                sortName, sort.getOrigin()));
            }

            int pos = doc.indexOf(DEFVALUE);
            if (pos >= 0) {
                int start = doc.indexOf('(', pos) + 1;
                int closing = doc.indexOf(')', pos);

                if (closing < 0) {
                    return reportError(n,
                            format(
                                    "Forgotten closing parenthesis on @defaultValue annotation for sort '%s' in '%s'",
                                    sortName, sort.getOrigin()));
                }

                // set this as the function name, as the user had written \dl_XXX
                name = doc.substring(start, closing);
            } else {
                return reportError(n,
                        format("Could not infer the default value for the given sort '%s'. " +
                                        "The sort found was as '%s' and the sort's documentation is '%s'. " +
                                        "Did you forget @defaultValue(XXX) in the documentation?",
                                sortName, sort, doc));
            }
        }

        ImmutableArray<Expression> args = map(arguments);

        return switch (name) {
            case "\\all_objects" -> new AllObjects(pi, c, args.get(0));
            case "\\all_fields" -> new AllFields(pi, c, args.get(0));
            case "\\intersect" -> new Intersect(pi, c, args.get(0), args.get(1));
            case "\\set_union" -> new SetUnion(pi, c, args.get(0), args.get(1));
            case "\\singleton" -> new Singleton(pi, c, args.get(0));
            case "\\set_minus" -> new SetMinus(pi, c, args.get(0), args.get(1));
            case "\\seq_sub" -> new SeqSub(pi, c, args.get(0), args.get(1), args.get(2));
            case "\\seq_reverse" -> new SeqReverse(pi, c, args.get(0));
            case "\\seq_singleton" -> new SeqSingleton(pi, c, args.get(0));
            case "\\seq_length" -> new SeqLength(pi, c, args.get(0));
            case "\\indexOf" -> new SeqIndexOf(pi, c, args.get(0), args.get(1));
            case "\\seq_concat" -> new SeqConcat(pi, c, args.get(0), args.get(1));
            case "\\seq_get" -> new SeqGet(pi, c, args.get(0), args.get(1));
            default -> {
                Function named = services.getNamespaces().functions().lookup(new org.key_project.logic.Name(name));
                if (named == null) {

    yield reportError(n, format("In an embedded DL expression, %s is not a known DL function name.", name));
                }yield new DLEmbeddedExpression(pi,c,(JFunction)named,new ImmutableArray<>());

    }};}

    private ImmutableArray<Expression> map(
            Optional<NodeList<com.github.javaparser.ast.expr.Expression>> arguments) {
        return arguments.<ImmutableArray<Expression>>map(this::map)
                .orElseGet(ImmutableArray::new);
    }

    @Override
    public Object visit(KeyExecStatement n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        StatementBlock body = accept(n.getExecBlock());
        ImmutableArray<Branch> branches = map(n.getBranches());
        return new Exec(pi, c, body, branches, null, 0);
    }

    @Override
    public Object visit(KeyExecutionContext n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        TypeReference classContext = requireTypeReference(n.getContext());
        ReferencePrefix runtimeInstance = accepto(n.getInstance());
        IProgramMethod methodContext =
            resolveMethodSignature(classContext.getKeYJavaType(), n.getSignature());
        if (methodContext == null) {
            return reportError(n, "Failed to resolve method");
        }
        return new ExecutionContext(pi, c, classContext, runtimeInstance, methodContext);
    }

    @Override
    public Object visit(KeyLoopScopeBlock n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        StatementBlock body = accept(n.getBlock());
        IProgramVariable indexPV = accept(n.getIndexPV());
        return new LoopScopeBlock(pi, c, indexPV, body, null, 0);
    }

    @Override
    public Object visit(KeyMergePointStatement n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        IProgramVariable expr = accept(n.getExpr());
        return new MergePointStatement(pi, c, null, expr);
    }

    @Override
    public Object visit(KeyMethodBodyStatement n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);

        MethodReference methodReference = accept(n.getExpr());
        TypeReference bodySource = requireTypeReference(n.getSource());
        IProgramVariable resultVar =
            n.getName().map(it -> (IProgramVariable) lookupSchemaVariable(it)).orElse(null);
        return new MethodBodyStatement(pi, c, resultVar, bodySource, methodReference);
    }

    @Override
    public Object visit(KeyMethodCallStatement n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        IProgramVariable resultVar = accepto(n.getName());
        StatementBlock body = accept(n.getBlock());
        IExecutionContext execContext = accept(n.getContext());
        PosInProgram firstActiveChildPos = null;
        // TODO weigl
        return new MethodFrame(pi, c, resultVar, body, execContext, firstActiveChildPos,
            0, null);
    }

    @Override
    public Object visit(KeyMethodSignature n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Nullable
    private IProgramMethod resolveMethodSignature(KeYJavaType type, KeyMethodSignature sig) {
        var name = sig.getName().asString();
        ImmutableArray<TypeReference> params = map(sig.getParamTypes());
        var paramTypes = params.stream().map(TypeReference::getKeYJavaType).toList();
        return services.getJavaInfo().getProgramMethod(type, name, paramTypes);
    }

    @Override
    public Object visit(KeyTransactionStatement n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new TransactionStatement(pi, c, n.getType());
    }

    @Override
    public Object visit(KeyContextStatementBlock n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        IExecutionContext execContext;
        if (n.getContext().isPresent()) {
            execContext = accepto(n.getContext());
        } else if (n.getTr().isPresent() || n.getSignature().isPresent()
                || n.getExpression().isPresent()) {
            if (n.getTr().isEmpty() || n.getSignature().isEmpty()) {
                return reportError(n, "No context type or method signature given");
            }
            var signature = n.getSignature().get();
            var execPi = createPositionInfo(signature);
            var execC = createComments(signature);
            TypeReference classContext = requireTypeReference(n.getTr().get());
            ReferencePrefix runtimeInstance = accepto(n.getExpression());
            IProgramMethod methodContext = accept(signature);
            execContext =
                new ExecutionContext(execPi, execC, classContext, runtimeInstance, methodContext);
        } else {
            execContext = null;
        }
        /*
         * TODO
         * if(execContext==null) {
         * //ExecutionContext Context: #t (program Type)##pm (program ProgramMethod) Instance: #v
         * (program Variable)
         * var t = lookupSchemaVariable("t", n); //type
         * var pm = lookupSchemaVariable("pm", n); // program method
         * var v = lookupSchemaVariable("v", n); // program var
         * execContext = new ExecutionContext((TypeReference) t, (IProgramMethod) pm,
         * (ReferencePrefix) v);
         * }
         */

        ImmutableArray<? extends Statement> body = map(n.getStatements());
        return new ContextStatementBlock(pi, c, body, execContext);
    }

    @Override
    public Object visit(KeyExpressionSV n, Void arg) {
        return lookupSchemaVariable(n.getText(), n);
    }

    @Override
    public Object visit(KeyMetaConstructExpression n, Void arg) {
        String mcName = n.getText();
        Expression child = accept(n.getChild());
        return switch (mcName) {
        case "#create-object" -> new CreateObject(child);
        case "#isstatic" -> new IsStatic(child);
        case "#length-reference" -> new ArrayLength(child);
        default -> reportError(n, "Program meta construct " + mcName + " unknown.");
        };
    }


    @Override
    public Object visit(KeyMetaConstruct n, Void arg) {
        String mcName = n.getKind();
        final ImmutableArray<SchemaVariable> labels = map(n.getSchemas());
        return switch (mcName) {
            case "#switch-to-if" -> new SwitchToIf(accept(n.getChild()));
            case "#unwind-loop" -> new UnwindLoop(labels.get(0), labels.get(1), accept(n.getChild()));
            case "#unpack" -> new Unpack(accept(n.getChild()));
            case "#forInitUnfoldTransformer" -> new ForInitUnfoldTransformer((ProgramSV) accept(n.getChild()));
            case "#for-to-while" -> new ForToWhile(labels.get(0), labels.get(1), accept(n.getChild()));
            case "#enhancedfor-elim" -> {
                EnhancedFor efor = accept(n.getChild());
                if (efor == null) {

    yield reportError(n,
                            "#enhancedfor-elim requires an enhanced for loop as argument");
                }

    ProgramSV execSV = null;for(
    var programSV:labels)
    {
        if (programSV.sort() == ProgramSVSort.EXECUTIONCONTEXT) {
            execSV = (ProgramSV) programSV;
            break;
        }
    }yield new EnhancedForElimination(execSV,efor);}case"#do-break"->new DoBreak(accept(n.getChild()));case"#expand-method-body"->new ExpandMethodBody((SchemaVariable)accept(n.getChild()));case"#method-call"->{
    ProgramSV execSV = null;
    ProgramSV returnSV = null;for(
    int i = 0;i<labels.size();i++)
    {
        final var sv = labels.get(i);
        if (sv.sort() == ProgramSVSort.VARIABLE) {
            returnSV = (ProgramSV) sv;
        }
        if (sv.sort() == ProgramSVSort.EXECUTIONCONTEXT) {
            execSV = (ProgramSV) sv;
        }
    }yield new MethodCall(execSV,returnSV,accept(n.getChild()));
    }case"#evaluate-arguments"->new EvaluateArgs(accept(n.getChild()));case"#constructor-call"->new ConstructorCall(labels.get(0),accept(n.getChild()));case"#special-constructor-call"->new SpecialConstructorCall(accept(n.getChild()));case"#post-work"->new PostWork((SchemaVariable)accept(n.getChild()));case"#static-initialisation"->new StaticInitialisation(accept(n.getChild()));case"#resolve-multiple-var-decl"->new MultipleVarDecl((SchemaVariable)n.getChild().accept(this,arg));case"#array-post-declaration"->new ArrayPostDecl((SchemaVariable)n.getChild().accept(this,arg));case"#init-array-creation"->new InitArrayCreation(labels.get(0),accept(n.getChild()));case"#reattachLoopInvariant"->new ReattachLoopInvariant(accept(n.getChild()));default->reportError(n,"Program meta construct "+n.getKind()+" unknown.");};}

    @Override
    public Object visit(KeyMetaConstructType n, Void arg) {
        Expression child = accept(n.getExpr());
        if ("#typeof".equals(n.getKind())) {
            return new TypeOf(child);
        } else {
            return reportError(n, "Program meta construct " + n.getKind() + " unknown.");
        }
    }


    @Override
    public Object visit(KeyPassiveExpression n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        // TODO weigl remove after fix of https://github.com/wadoon/key-javaparser/issues/2
        n.getExpr().setParentNode(n);
        return new PassiveExpression(pi, c, accept(n.getExpr()));
    }

    // region Unsupported AST Classes
    @Override
    public Object visit(LocalClassDeclarationStmt n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(LocalRecordDeclarationStmt n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(TypeParameter n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(AnnotationDeclaration n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(AnnotationMemberDeclaration n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(ClassExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        TypeReference rt = accept(n.getType());
        return new MetaClassReference(pi, c, rt);
    }

    @Override
    public Object visit(EnumConstantDeclaration n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(EnumDeclaration n, Void arg) {
        // Important: get the kjt of n.resolve() and setKeYJavaType with the resulting KeY
        // declaration
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(JavadocComment n, Void arg) {
        return reportUnsupportedElement(n);
    }


    @Override
    public Object visit(MarkerAnnotationExpr n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(MemberValuePair n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(WildcardType n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(LambdaExpr n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(MethodReferenceExpr n, Void arg) {
        return reportUnsupportedElement(n);
    }


    @Override
    public Object visit(ModuleDeclaration n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(ModuleRequiresDirective n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(ModuleExportsDirective n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(ModuleProvidesDirective n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(ModuleUsesDirective n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(ModuleOpensDirective n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(UnparsableStmt n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(ReceiverParameter n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(VarType n, Void arg) {
        return getKeYJavaType(n.resolve());
    }

    @Override
    public Object visit(SwitchExpr n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(YieldStmt n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(TextBlockLiteralExpr n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(PatternExpr n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(RecordDeclaration n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(CompactConstructorDeclaration n, Void arg) {
        return reportUnsupportedElement(n);
    }

    @Override
    public Object visit(KeyRangeExpression n, Void arg) {
        return reportUnsupportedElement(n);
    }
    // endregion

    @Override
    public SchemaVariable visit(KeyMethodSignatureSV n, Void arg) {
        return lookupSchemaVariable(n.getText(), n);
    }

    @Override
    public SchemaVariable visit(KeyProgramVariableSV n, Void arg) {
        return lookupSchemaVariable(n.getText(), n);
    }

    @Override
    public SchemaVariable visit(KeyStatementSV n, Void arg) {
        return lookupSchemaVariable(n.getText(), n);
    }

    @Override
    public SchemaVariable visit(KeyTypeSV n, Void arg) {
        return lookupSchemaVariable(n.getText(), n);
    }

    @Override
    public SchemaVariable visit(KeyCcatchSV n, Void arg) {
        return lookupSchemaVariable(n.getText(), n);
    }

    @Override
    public SchemaVariable visit(KeyExecutionContextSV n, Void arg) {
        return lookupSchemaVariable(n.getText(), n);
    }

    @Override
    public SchemaVariable visit(KeyExecCtxtSV n, Void arg) {
        return lookupSchemaVariable(n.getText(), n);
    }

    @Override
    public SchemaVariable visit(KeyJumpLabelSV n, Void arg) {
        return lookupSchemaVariable(n.getText(), n);
    }

    private SchemaVariable lookupSchemaVariable(Name name) {
        return lookupSchemaVariable(name.asString(), name);
    }

    private SchemaVariable lookupSchemaVariable(SimpleName name) {
        return lookupSchemaVariable(name.asString(), name);
    }

    @NonNull
    private SchemaVariable lookupSchemaVariable(String name, Node context) {
        SchemaVariable n = schemaVariableNamespace.lookup(new org.key_project.logic.Name(name));
        if (n != null) {
            return n;
        } else {
            return reportError(context, "Schema variable not declared: " + name);
        }
    }

    private record FullVariableDeclarator(VariableDeclarator decl, boolean isFinal,
            boolean isStatic, boolean isModel) {
    }

}
