package de.uka.ilkd.key.java;

import com.github.javaparser.ast.Modifier;
import com.github.javaparser.ast.*;
import com.github.javaparser.ast.body.ConstructorDeclaration;
import com.github.javaparser.ast.body.FieldDeclaration;
import com.github.javaparser.ast.body.MethodDeclaration;
import com.github.javaparser.ast.body.*;
import com.github.javaparser.ast.comments.JavadocComment;
import com.github.javaparser.ast.expr.*;
import com.github.javaparser.ast.key.*;
import com.github.javaparser.ast.key.sv.*;
import com.github.javaparser.ast.modules.*;
import com.github.javaparser.ast.stmt.*;
import com.github.javaparser.ast.type.*;
import com.github.javaparser.ast.visitor.GenericVisitorAdapter;
import com.github.javaparser.ast.visitor.Visitable;
import com.github.javaparser.resolution.types.ResolvedArrayType;
import com.github.javaparser.resolution.types.ResolvedPrimitiveType;
import com.github.javaparser.resolution.types.ResolvedReferenceType;
import com.github.javaparser.resolution.types.ResolvedType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.*;
import de.uka.ilkd.key.java.declaration.modifier.*;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.ProgramSVSort;
import de.uka.ilkd.key.logic.sort.Sort;
import de.uka.ilkd.key.rule.metaconstruct.*;
import de.uka.ilkd.key.util.parsing.BuildingExceptions;
import de.uka.ilkd.key.util.parsing.BuildingIssue;
import org.key_project.util.collection.ImmutableArray;

import javax.annotation.Nullable;
import java.net.URI;
import java.util.*;
import java.util.stream.Collectors;

import static java.lang.String.format;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public class JP2KeyConverter {
    private final Services services;
    private final KeyJPMapping mapping;
    private final Namespace<SchemaVariable> schemaVariables;

    public JP2KeyConverter(Services services, KeyJPMapping mapping, Namespace<SchemaVariable> schemaVariables) {
        this.services = services;
        this.mapping = mapping;
        this.schemaVariables = schemaVariables;
    }

    public CompilationUnit processCompilationUnit(com.github.javaparser.ast.CompilationUnit cu) {
        return (CompilationUnit) process(cu);
    }

    public Object process(Node block) {
        return block.accept(new JP2KeyVisitor(services, mapping, schemaVariables), null);
    }
}

class JP2KeyVisitor extends GenericVisitorAdapter<Object, Void> {
    private final Services services;
    private final KeyJPMapping mapping;
    private final Namespace<SchemaVariable> svns;
    private Map<String, KeYJavaType> types = new TreeMap<>();

    JP2KeyVisitor(Services services, KeyJPMapping mapping, Namespace<SchemaVariable> schemaVariables) {
        this.services = services;
        this.mapping = mapping;
        svns = schemaVariables;
    }

    private void reportError(Node n, String message) {
        var line = n.getRange().map(it -> it.begin).map(it -> it.line).orElse(-1);
        var posInLine = n.getRange().map(it -> it.begin).map(it -> it.column).orElse(-1);
        var loc = n.findCompilationUnit()
                .flatMap(it -> it.getStorage()).map(it -> it.getPath().toUri()).orElse(null);
        BuildingIssue problem =
                new BuildingIssue(message,
                        null, false, line, posInLine, -1, -1, loc);
        throw new BuildingExceptions(Collections.singletonList(problem));
    }

    private void reportUnsupportedElement(Node n) {
        reportError(n, "Unsupported element detected given by Java Parser: "
                + n.getMetaModel().getTypeName() + ". Please extend the KeY-Java-Hierarchy");
    }

    @Override
    public Object visit(ArrayAccessExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Expression expr = accept(n.getIndex());
        Expression prefix = accept(n.getName());
        //TODO weigl how to express (new int[0])[0] in Java-KeY-AST?
        return new ArrayReference(pi, c, (ReferencePrefix) prefix,
                new ImmutableArray<>(expr));
    }

    @Override
    public Object visit(ArrayCreationExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ImmutableArray<Expression> children = map(n.getLevels());
        TypeReference type = accept(n.getElementType());
        ArrayInitializer ai = accepto(n.getInitializer());
        var rtype = n.calculateResolvedType();
        return new NewArray(pi, c, children, type, getKeyJavaType(rtype), 0/*TODO*/, ai);
    }

    @Override
    public Object visit(ArrayInitializerExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ImmutableArray<Expression> children = map(n.getValues());
        var rtype = n.calculateResolvedType();
        return new ArrayInitializer(pi, c, children, getKeyJavaType(rtype));
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
        switch (n.getOperator()) {
            case ASSIGN:
                return new CopyAssignment(pi, c, target, expr);
            case PLUS:
                return new PlusAssignment(pi, c, target, expr);
            case MINUS:
                return new MinusAssignment(pi, c, target, expr);
            case MULTIPLY:
                return new TimesAssignment(pi, c, target, expr);
            case DIVIDE:
                return new DivideAssignment(pi, c, target, expr);
            case BINARY_AND:
                return new BinaryAndAssignment(pi, c, target, expr);
            case BINARY_OR:
                return new BinaryOrAssignment(pi, c, target, expr);
            case XOR:
                return new BinaryXOrAssignment(pi, c, target, expr);
            case REMAINDER:
                return new ModuloAssignment(pi, c, target, expr);
            case LEFT_SHIFT:
                return new ShiftLeftAssignment(pi, c, target, expr);
            case SIGNED_RIGHT_SHIFT:
                return new UnsignedShiftRightAssignment(pi, c, target, expr);
            case UNSIGNED_RIGHT_SHIFT:
                return new ShiftRightAssignment(pi, c, target, expr);
        }
        return null;
    }

    @Override
    public Object visit(BinaryExpr n, Void arg) {
        var lhs = (Expression) n.getLeft().accept(this, arg);
        var rhs = (Expression) n.getRight().accept(this, arg);
        var pi = createPositionInfo(n);
        var c = createComments(n);
        switch (n.getOperator()) {
            case OR:
                return new LogicalOr(pi, c, lhs, rhs);
            case AND:
                return new LogicalAnd(pi, c, lhs, rhs);
            case BINARY_OR:
                return new BinaryOr(pi, c, lhs, rhs);
            case BINARY_AND:
                return new BinaryAnd(pi, c, lhs, rhs);
            case XOR:
                return new BinaryXOr(pi, c, lhs, rhs);
            case EQUALS:
                return new Equals(pi, c, lhs, rhs);
            case NOT_EQUALS:
                return new NotEquals(pi, c, lhs, rhs);
            case LESS:
                return new LessThan(pi, c, lhs, rhs);
            case GREATER:
                return new GreaterThan(pi, c, lhs, rhs);
            case LESS_EQUALS:
                return new LessOrEquals(pi, c, lhs, rhs);
            case GREATER_EQUALS:
                return new GreaterOrEquals(pi, c, lhs, rhs);
            case LEFT_SHIFT:
                return new ShiftLeft(pi, c, lhs, rhs);
            case SIGNED_RIGHT_SHIFT:
                return new ShiftRight(pi, c, lhs, rhs);
            case UNSIGNED_RIGHT_SHIFT:
                return new UnsignedShiftRight(pi, c, lhs, rhs);
            case PLUS:
                return new Plus(pi, c, lhs, rhs);
            case MINUS:
                return new Minus(pi, c, lhs, rhs);
            case MULTIPLY:
                return new Times(pi, c, lhs, rhs);
            case DIVIDE:
                return new Divide(pi, c, lhs, rhs);
            case REMAINDER:
                return new Modulo(pi, c, lhs, rhs);
        }
        return null;
    }

    @Override
    public Object visit(BlockStmt n, Void arg) {
        ImmutableArray<Statement> body = map(n.getStatements());
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new StatementBlock(pi, c, body, 0, null);
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
        return new TypeCast(pi, c, accept(n.getExpression()), accept(n.getType()));
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
        ProgramElementName name = new ProgramElementName(n.getNameAsString());
        ProgramElementName fullName = new ProgramElementName(n.getFullyQualifiedName().get());
        boolean isLibrary = false; //TODO weigl
        ImmutableArray<de.uka.ilkd.key.java.declaration.Modifier> modArray = map(n.getModifiers());
        ImmutableArray<MemberDeclaration> members = map(n.getMembers());
        boolean parentIsInterface = false;

        ImmutableArray<TypeReference> e = map(n.getExtendedTypes());
        ImmutableArray<TypeReference> i = map(n.getImplementedTypes());
        Extends extending = new Extends(e);
        Implements implementing = new Implements(i);

        if (n.isInterface()) {
            return new InterfaceDeclaration(
                    pi, c, modArray, name, fullName, members,
                    parentIsInterface, isLibrary, extending);
        } else {
            return new ClassDeclaration(pi, c, modArray, name, fullName, members, parentIsInterface,
                    isLibrary, extending, implementing, n.isInnerClass(), n.isLocalClassDeclaration(), false);
        }
    }

    /*private ExtList visitChildren(Node node) {
        ExtList seq = new ExtList(node.getChildNodes().size());
        for (Node childNode : node.getChildNodes()) {
            var element = childNode.accept(this, null);
            if (element != null) {
                seq.add(element);
            }
        }
        seq.add(createPositionInfo(node));
        return seq;
    }*/


    private <T extends Object> T accept(Node check) {
        var a = check.accept(this, null);
        mapping.put(check, a);
        return (T) a;
    }

    private PositionInfo createPositionInfo(Node node) {
        if (node.getRange().isEmpty()) {
            return null;
        }
        var r = node.getRange().get();

        URI uri = node.findCompilationUnit().flatMap(it ->
                it.getStorage()).map(it -> it.getPath().toUri()).orElse(null);
        Position relPos = new Position(-1, -1);
        Position startPos = new Position(r.begin.line, r.begin.column);
        Position endPos = new Position(r.end.line, r.end.column);
        return new PositionInfo(relPos, startPos, endPos, uri);
    }

    @Override
    public Object visit(ClassOrInterfaceType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(com.github.javaparser.ast.CompilationUnit n, Void arg) {
        return new CompilationUnit(
                createPositionInfo(n), createComments(n),
                accepto(n.getPackageDeclaration()),
                map(n.getImports()),
                map(n.getTypes()));
    }

    private List<Comment> createComments(Node n) {
        //TODO weigl
        return Collections.emptyList();
    }

    private <T> ImmutableArray<T> map(NodeList<? extends Visitable> nodes) {
        var seq = nodes.stream().map(it -> (T) it.accept(this, null)).collect(Collectors.toList());
        return new ImmutableArray<>(seq);
    }

    @Nullable
    private <R> R accepto(Optional<? extends Node> node) {
        if (node.isEmpty()) return null;
        return accept(node.get());
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
        boolean parentIsInterface = false;
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ImmutableArray<TypeReference> exc = map(n.getThrownExceptions());
        Throws thr = exc.isEmpty() ? null : new Throws(null, null, exc);
        return new de.uka.ilkd.key.java.declaration.ConstructorDeclaration(pi, c,
                map(n.getModifiers()),
                null,
                null,
                new ProgramElementName(n.getNameAsString()),
                map(n.getParameters()),
                thr,
                accept(n.getBody()), false);
    }

    @Override
    public Object visit(ContinueStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Label name = simpleNameToLabel(n.getLabel());
        return new Continue(pi, c, name);
    }

    private Label nameToLabel(Optional<Name> label) {
        return label.map(name -> new ProgramElementName(name.asString())).orElse(null);
    }

    private Label simpleNameToLabel(Optional<SimpleName> label) {
        return label.map(name -> new ProgramElementName(name.asString())).orElse(null);
    }

    @Override
    public Object visit(DoStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        var guard = accept(n.getCondition());
        var body = accept(n.getBody());
        return new Do(pi, c, new Guard((Expression) guard), (Statement) body);
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
        return super.visit(n, arg);
    }

    @Override
    public Object visit(ExpressionStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return accept(n.getExpression());
    }

    @Override
    public Object visit(FieldAccessExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        var rtype = n.calculateResolvedType();
        var kjt = getKeyJavaType(rtype);

        ProgramVariable variable = new LocationVariable(
                new ProgramElementName(n.getNameAsString()), kjt);
        ReferencePrefix prefix = accept(n.getScope());
        return new FieldReference(pi, c, variable, prefix);
    }

    private KeYJavaType getKeyJavaType(ResolvedType rtype) {
        if (rtype.isVoid()) {
            return KeYJavaType.VOID_TYPE;
        }

        if (rtype.isPrimitive()) {
            ResolvedPrimitiveType ptype = rtype.asPrimitive();
            switch (ptype) {
                case BYTE:
                    break;
                case SHORT:
                    break;
                case CHAR:
                    break;
                case INT:
                    break;
                case LONG:
                    break;
                case BOOLEAN:
                    break;
                case FLOAT:
                    break;
                case DOUBLE:
                    break;
            }
        }

        if (types.containsKey(rtype.describe())) {
            return types.get(rtype.describe());
        }

        if (rtype.isReferenceType()) {
            var t = createKeyJavaType(rtype.asReferenceType());
            types.put(rtype.describe(), t);
        }

        if (rtype.isArray()) {
            var t = createKeyJavaType(rtype.asArrayType());
            types.put(rtype.describe(), t);
        }

        if (rtype.isNull()) {

        }
        return new KeYJavaType();
    }

    private KeYJavaType createKeyJavaType(ResolvedArrayType asArrayType) {
        var rbase = asArrayType.getComponentType();
        //TypeReference baseType = getKeyJavaType(rbase).getJavaType();
        //ArrayDeclaration ad = new ArrayDeclaration(null, baseType, null/*TODO*/);
        //TODO weigl how to create a proper type?
        return new KeYJavaType();
    }

    private KeYJavaType createKeyJavaType(ResolvedReferenceType rtype) {
        var sort = services.getNamespaces().sorts().lookup(rtype.getQualifiedName());
        //TODO weigl how to create a proper type?
        de.uka.ilkd.key.java.abstraction.Type type = null;
        return new KeYJavaType(type, sort);
    }

    @Override
    public Object visit(FieldDeclaration n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        boolean parentIsInferface = false;
        ImmutableArray<de.uka.ilkd.key.java.declaration.Modifier> modArray = map(n.getModifiers());
        TypeReference type = accept(n.getVariables().get(0).getType());
        ImmutableArray<FieldSpecification> fieldSpecs = map(n.getVariables());
        return new de.uka.ilkd.key.java.declaration.FieldDeclaration(pi, c, modArray, type, parentIsInferface, fieldSpecs);
    }

    @Override
    public Object visit(ForEachStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ILoopInit init = accept(n.getVariable());
        Guard guard = new Guard(null, null, accept(n.getIterable()));
        return new EnhancedFor(pi, c, init, guard, accept(n.getBody()));
    }

    @Override
    public Object visit(ForStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ImmutableArray<LoopInitializer> inits = map(n.getInitialization());
        ImmutableArray<Expression> update = map(n.getUpdate());
        Guard guard = new Guard(pi, null, accepto(n.getCompare()));
        final var loopInit = new LoopInit(inits);
        return new For(pi, c, loopInit, new ForUpdates(update), guard, accept(n.getBody()));
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
        return super.visit(n, arg);
    }

    @Override
    public Object visit(InstanceOfExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        var lhs = (Expression) accept(n.getExpression());
        var type = (TypeReference) accept(n.getType());
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
        var id = accept(n.getLabel());
        var stmt = accept(n.getStatement());
        return new LabeledStatement((Label) id, (Statement) stmt, createPositionInfo(n));
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
        ReferencePrefix prefix = accepto(n.getScope());
        MethodName name = new ProgramElementName(n.getNameAsString());
        ImmutableArray<Expression> args = map(n.getArguments());
        return new MethodReference(pi, c, prefix, name, args);
    }

    @Override
    public Object visit(MethodDeclaration n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);

        ImmutableArray<TypeReference> t = map(n.getThrownExceptions());
        var thr = t.isEmpty() ? null : new Throws(null, null, t);
        boolean parentIsInterface = false;
        return new de.uka.ilkd.key.java.declaration.MethodDeclaration(
                pi, c, map(n.getModifiers()),
                accept(n.getType()),
                null,
                new ProgramElementName(n.getNameAsString()),
                map(n.getParameters()),
                thr,
                accepto(n.getBody()),
                parentIsInterface);
    }

    @Override
    public Object visit(NameExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        ResolvedType rtype = n.calculateResolvedType();
        //TODO weigl find declaraton with n.resolve()
        return new LocationVariable(new ProgramElementName(n.getNameAsString()), getKeyJavaType(rtype));
    }

    @Override
    public Object visit(NormalAnnotationExpr n, Void arg) {
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
        return super.visit(n, arg);
    }

    @Override
    public Object visit(PackageDeclaration n, Void arg) {
        if (n.getAnnotations().isNonEmpty()) reportUnsupportedElement(n);

        ProgramElementName name = translateName(n.getName());
        ReferencePrefix prefix = null;//TODO
        return new PackageSpecification(new PackageReference(name, prefix));
    }

    private ProgramElementName translateName(Name name) {
        return new ProgramElementName(name.asString());
    }

    @Override
    public Object visit(Parameter n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(PrimitiveType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(Name n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(SimpleName n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(ArrayType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(ArrayCreationLevel n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(IntersectionType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(UnionType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(ReturnStmt n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(SingleMemberAnnotationExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(StringLiteralExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(SuperExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(SwitchEntry n, Void arg) {
        n.getLabels();
        n.getStatements();
        n.getType();
        //TODO return new Case(e, body);
        return null;
    }

    @Override
    public Object visit(SwitchStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Expression expr = null; //TODO
        ImmutableArray<Branch> branches = map(n.getEntries());
        return new Switch(pi, c, expr, branches);
    }

    @Override
    public Object visit(SynchronizedStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new SynchronizedBlock(pi, c, accept(n.getExpression()), accept(n.getBody()),
                null, 0);
    }

    @Override
    public Object visit(ThisExpr n, Void arg) {
        n.getTypeName();//TODO
        return new ThisReference(createPositionInfo(n), createComments(n), null);
    }

    @Override
    public Object visit(ThrowStmt n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(TryStmt n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        StatementBlock body = accept(n.getTryBlock());
        ImmutableArray<Branch> branches = map(n.getCatchClauses());
        //TODO weigl add finally clauses to branches
        return new Try(pi, c, body, branches, null, 0);
    }


    @Override
    public Object visit(UnaryExpr n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Expression child = accept(n.getExpression());
        switch (n.getOperator()) {
            case PLUS:
                return new Positive(pi, c, child);
            case MINUS:
                return new Negative(pi, c, child);
            case PREFIX_INCREMENT:
                return new PreIncrement(pi, c, child);
            case PREFIX_DECREMENT:
                return new PreDecrement(pi, c, child);
            case LOGICAL_COMPLEMENT:
                return new LogicalNot(pi, c, child);
            case BITWISE_COMPLEMENT:
                return new BinaryNot(pi, c, child);
            case POSTFIX_INCREMENT:
                return new PostIncrement(pi, c, child);
            case POSTFIX_DECREMENT:
                return new PostDecrement(pi, c, child);
        }
        return null;
    }

    @Override
    public Object visit(UnknownType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(VariableDeclarationExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(VariableDeclarator n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public Object visit(VoidType n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return null; /*TODO*/
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
            reportUnsupportedElement(n);
        }

        if (n.isAsterisk()) {
            var name = translateName(n.getName());
            return new Import(new PackageReference(name, null));
        } else {
            TypeReference type = null; //TODO weigl
            return new Import(type, n.isAsterisk());
        }
    }

    @Override
    public Object visit(Modifier n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        var k = n.getKeyword();
        switch (k) {
            case DEFAULT:
                reportUnsupportedElement(n);
                break;
            case PUBLIC:
                return new Public(/*pi, c*/);
            case PROTECTED:
                return new Protected(/*pi, c*/);
            case PRIVATE:
                return new Private(/*pi, c*/);
            case ABSTRACT:
                return new Abstract(/*pi, c*/);
            case STATIC:
                return new Static(/*pi, c*/);
            case FINAL:
                return new Final(/*pi, c*/);
            case TRANSIENT:
                return new Transient(/*pi, c*/);
            case VOLATILE:
                return new Volatile(/*pi, c*/);
            case SYNCHRONIZED:
                return new Synchronized(/*pi, c*/);
            case NATIVE:
                return new Native(/*pi, c*/);
            case STRICTFP:
                return new StrictFp(/*pi, c*/);
            case TRANSITIVE:
                reportUnsupportedElement(n);
                break;
            case GHOST:
                return new Ghost(/*pi, c*/);
            case MODEL:
                return new Model(/*pi, c*/);
            case TWO_STATE:
                return new TwoState(/*pi, c*/);
            case NO_STATE:
                return new NoState(/*pi, c*/);
        }
        return null;
    }


    //region ccatch
    @Override
    public Object visit(KeyCcatchBreak n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        if (n.getLabel().isPresent()) {
            var label = nameToLabel(n.getLabel());
            return new CcatchBreakLabelParameterDeclaration(pi, c, label);
        }
        if (n.getBlock().isPresent()) {
            return new CcatchBreakParameterDeclaration(pi, c);
        }
        return new CcatchBreakWildcardParameterDeclaration(pi, c);
    }

    @Override
    public Object visit(KeyCcatchContinue n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        if (n.getLabel().isPresent()) {
            var label = nameToLabel(n.getLabel());
            return new CcatchContinueLabelParameterDeclaration(pi, c, label);
        }
        if (n.getBlock().isPresent()) {
            return new CcatchContinueParameterDeclaration(pi, c);
        }
        return new CcatchContinueWildcardParameterDeclaration(pi, c);
    }

    @Override
    public Object visit(KeyCcatchParameter n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        //TODO
        return null;
    }

    @Override
    public Object visit(KeyCcatchReturn n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        if (n.getParameter().isPresent()) {
            ParameterDeclaration delegate = null;
            return new CcatchReturnValParameterDeclaration(pi, c, delegate);
        }
        return new CcatchReturnParameterDeclaration(pi, c);
    }

    @Override
    public Object visit(KeyCatchAllStatement n, Void arg) {
        //TODO
        return super.visit(n, arg);
    }
    //endregion

    @Override
    public Object visit(KeyEscapeExpression n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);

        final var PREFIX = "\\dl_DEFAULT_VALUE_";
        final var DEFVALUE = "@defaultValue(";
        String name = n.getCallee().asString();

        if (name.startsWith(PREFIX)) { // handle default value resolution
            String sortName = name.substring(PREFIX.length()).trim();
            Sort sort = services.getNamespaces().sorts().lookup(sortName);
            if (sort == null) {
                reportError(n, format("Requested to find the default value of an unknown sort '%s'.", sortName));
            }

            var doc = sort.getDocumentation();

            if (doc == null) {
                reportError(n,
                        format("Requested to find the default value for the sort '%s', " +
                                        "which does not have a documentary comment. The sort is defined at %s. "
                                , sortName, sort.getOrigin()));
            }

            int pos = doc.indexOf(DEFVALUE);
            if (pos >= 0) {
                int start = doc.indexOf('(', pos) + 1;
                int closing = doc.indexOf(')', pos);

                if (closing < 0) {
                    throw new ConvertException(
                            format("Forgotten closing parenthesis on @defaultValue annotation for sort '%s' in '%s'",
                                    sortName, sort.getOrigin()));
                }

                // set this as the function name, as the user had written \dl_XXX
                name = doc.substring(start, closing);
            } else {
                throw new ConvertException(
                        format("Could not infer the default value for the given sort '%s'. " +
                                        "The sort found was as '%s' and the sort's documentation is '%s'. " +
                                        "Did you forget @defaultValue(XXX) in the documentation? Line/Col: %s",
                                sortName, sort, doc, null));
            }
        }

        Function named = services.getNamespaces().functions().lookup(new de.uka.ilkd.key.logic.Name(name));

        if (named == null) {
            reportError(n, format("In an embedded DL expression, %s is not a known DL function name.", name));
        }

        if (n.getArguments().isPresent()) {
            ImmutableArray<Expression> args = map(n.getArguments().get());
            return new DLEmbeddedExpression(pi, c, named, args);
        }
        return new DLEmbeddedExpression(pi, c, named, new ImmutableArray<>());
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
        TypeReference classContext = accept(n.getContext());
        ReferencePrefix runtimeInstance = accepto(n.getInstance());
        IProgramMethod methodContext = accept(n.getSignature());
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
        IProgramVariable ident = accept(n.getExpr());
        return new MergePointStatement(pi, c, ident);
    }

    @Override
    public Object visit(KeyMethodBodyStatement n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        IProgramVariable resultVar = accept(n.getExpr());
        TypeReference bodySource = accept(n.getSource());
        MethodReference methodReference = null;//TODO missing?
        IProgramMethod method = null;
        return new MethodBodyStatement(pi, c, resultVar, bodySource, methodReference, method);
    }

    @Override
    public Object visit(KeyMethodCallStatement n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        IProgramVariable resultVar = null;
        StatementBlock body = null;
        IExecutionContext execContext = null;
        PosInProgram firstActiveChildPos = null;
        //TODO weigl
        return new MethodFrame(pi, c, resultVar, body, execContext, firstActiveChildPos,
                0, null);
    }

    @Override
    public Object visit(KeyMethodSignature n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        //TODO weigl unclear
        return null;
    }

    @Override
    public Object visit(KeyTransactionStatement n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new TransactionStatement(pi, c, n.getType().ordinal());
    }

    @Override
    public Object visit(KeyContextStatementBlock n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        IExecutionContext execContext = accepto(n.getContext());
        ImmutableArray<? extends Statement> body = map(n.getStatements());
        //TODO weigl prefixLength constants
        return new ContextStatementBlock(pi, c, body, 0, null, execContext, 0);
    }


    @Override
    public Object visit(KeyExpressionSV n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return super.visit(n, arg);
    }


    @Override
    public Object visit(KeyMetaConstructExpression n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        String mcName = n.getText();
        Expression child = accept(n.getChild());
        switch (mcName) {
            case "#create-object":
                return new CreateObject(child);
            case "#isstatic":
                return new IsStatic(child);
            case "#length-reference":
                return new ArrayLength(child);
            default:
                reportError(n, "Program meta construct " + mcName + " unknown.");
        }
        return null;
    }


    @Override
    public Object visit(KeyMetaConstruct n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        String mcName = n.getKind();
        final ImmutableArray<SchemaVariable> labels = map(n.getSchemas());
        switch (mcName) {
            case "#switch-to-if":
                return new SwitchToIf(labels.get(0));
            case "#unwind-loop": {
                return new UnwindLoop(labels.get(0), labels.get(1), accept(n.getChild()));
            }
            case "#unpack":
                return new Unpack(accept(n.getChild()));
            case "#forInitUnfoldTransformer":
                return new ForInitUnfoldTransformer((ProgramSV) labels.get(0));
            case "#for-to-while": {
                return new ForToWhile(labels.get(0), labels.get(1), accept(n.getChild()));
            }
            case "#enhancedfor-elim": {
                EnhancedFor efor = accept(n.getChild());
                if (efor == null) {
                    reportError(n, "#enhancedfor-elim requires an enhanced for loop as argument");
                }
                ProgramSV execSV = null;
                for (var programSV : labels) {
                    if (programSV.sort() == ProgramSVSort.EXECUTIONCONTEXT) {
                        execSV = (ProgramSV) programSV;
                        break;
                    }
                }
                return new EnhancedForElimination(execSV, efor);
            }
            case "#do-break":
                return new DoBreak(accept(n.getChild()));
            case "#expand-method-body":
                return new ExpandMethodBody(labels.get(0));
            case "#method-call": {
                ProgramSV execSV = null;
                ProgramSV returnSV = null;
                for (int i = 0; i < labels.size(); i++) {
                    final var sv = labels.get(i);
                    if (sv.sort() == ProgramSVSort.VARIABLE) {
                        returnSV = (ProgramSV) sv;
                    }
                    if (sv.sort() == ProgramSVSort.EXECUTIONCONTEXT) {
                        execSV = (ProgramSV) sv;
                    }
                }
                return new MethodCall(execSV, returnSV, accept(n.getChild()));
            }
            case "#evaluate-arguments":
                return new EvaluateArgs(accept(n.getChild()));
            case "#constructor-call":
                return new ConstructorCall(labels.get(0), accept(n.getChild()));
            case "#special-constructor-call":
                return new SpecialConstructorCall(accept(n.getChild()));
            case "#post-work":
                return new PostWork(labels.get(0));
            case "#static-initialisation":
                return new StaticInitialisation(accept(n.getChild()));
            case "#resolve-multiple-var-decl":
                return new MultipleVarDecl(labels.get(0));
            case "#array-post-declaration":
                return new ArrayPostDecl(labels.get(0));
            case "#init-array-creation":
                return new InitArrayCreation(labels.get(0), accept(n.getChild()));
            case "#reattachLoopInvariant":
                return new ReattachLoopInvariant(accept(n.getChild()));
            default:
                reportError(n, "Program meta construct " + n.getKind() + " unknown.");
        }
        return null;
    }

    @Override
    public Object visit(KeyMetaConstructType n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        Expression child = accept(n.getExpr());
        if ("#typeof".equals(n.getKind())) {
            return new TypeOf(child);
        } else {
            reportError(n, "Program meta construct " + n.getKind() + " unknown.");
            return null;
        }
    }


    @Override
    public Object visit(KeyPassiveExpression n, Void arg) {
        var pi = createPositionInfo(n);
        var c = createComments(n);
        return new PassiveExpression(pi, c, accept(n.getExpr()));
    }

    //region Unsupported AST Classes
    @Override
    public Object visit(LocalClassDeclarationStmt n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(LocalRecordDeclarationStmt n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(TypeParameter n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(AnnotationDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(AnnotationMemberDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(ClassExpr n, Void arg) {
        reportUnsupportedElement(n);
        return null;
    }

    @Override
    public Object visit(EnumConstantDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(EnumDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(JavadocComment n, Void arg) {
        reportUnsupportedElement(n);
        return null;
    }


    @Override
    public Object visit(MarkerAnnotationExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(MemberValuePair n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(WildcardType n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(LambdaExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(MethodReferenceExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(TypeExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }


    @Override
    public Object visit(ModuleDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(ModuleRequiresDirective n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(ModuleExportsDirective n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(ModuleProvidesDirective n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(ModuleUsesDirective n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(ModuleOpensDirective n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(UnparsableStmt n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(ReceiverParameter n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(VarType n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(SwitchExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(YieldStmt n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(TextBlockLiteralExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(PatternExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(RecordDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(CompactConstructorDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public Object visit(KeyRangeExpression n, Void arg) {
        reportUnsupportedElement(n);
        return null;
    }
    //endregion

    @Override
    public SchemaVariable visit(KeyMethodSignatureSV n, Void arg) {
        return lookupSchemaVariable(n.getText());
    }

    @Override
    public SchemaVariable visit(KeyProgramVariableSV n, Void arg) {
        return lookupSchemaVariable(n.getText());
    }

    @Override
    public SchemaVariable visit(KeyStatementSV n, Void arg) {
        return lookupSchemaVariable(n.getText());
    }

    @Override
    public SchemaVariable visit(KeyTypeSV n, Void arg) {
        return lookupSchemaVariable(n.getName());
    }

    @Override
    public SchemaVariable visit(KeyCcatchSV n, Void arg) {
        return lookupSchemaVariable(n.getText());
    }

    @Override
    public SchemaVariable visit(KeyExecutionContextSV n, Void arg) {
        return lookupSchemaVariable(n.getText());
    }

    @Override
    public SchemaVariable visit(KeyExecCtxtSV n, Void arg) {
        return lookupSchemaVariable(n.getText());
    }

    @Override
    public SchemaVariable visit(KeyJumpLabelSV n, Void arg) {
        return lookupSchemaVariable(n.getText());
    }

    private SchemaVariable lookupSchemaVariable(String name) {
        SchemaVariable n = svns.lookup(new de.uka.ilkd.key.logic.Name(name));
        if (n != null) {
            return n;
        } else {
            throw new IllegalArgumentException("Schema variable not declared: " + name);
        }
    }
}