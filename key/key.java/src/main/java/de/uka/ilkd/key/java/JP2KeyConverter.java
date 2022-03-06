package de.uka.ilkd.key.java;

import com.github.javaparser.ast.*;
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
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.java.declaration.InterfaceDeclaration;
import de.uka.ilkd.key.java.declaration.modifier.*;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.*;
import de.uka.ilkd.key.java.expression.operator.*;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.util.parsing.BuildingExceptions;
import de.uka.ilkd.key.util.parsing.BuildingIssue;
import org.key_project.util.ExtList;

import javax.annotation.Nullable;
import java.net.URI;
import java.util.Collections;
import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (05.03.22)
 */
public class JP2KeyConverter {
    private final Services services;
    private final KeyJPMapping mapping;

    public JP2KeyConverter(Services services, KeyJPMapping mapping) {
        this.services = services;
        this.mapping = mapping;
    }

    public CompilationUnit processCompilationUnit(com.github.javaparser.ast.CompilationUnit cu) {
        return (CompilationUnit) process(cu);
    }

    public Object process(Node block) {
        return block.accept(new JP2KeyVisitor(mapping), null);
    }
}

class JP2KeyVisitor extends GenericVisitorAdapter<ModelElement, Void> {
    private final KeyJPMapping mapping;

    JP2KeyVisitor(KeyJPMapping mapping) {
        this.mapping = mapping;
    }

    private void reportUnsupportedElement(Node n) {
        var line = n.getRange().map(it -> it.begin).map(it -> it.line).orElse(-1);
        var posInLine = n.getRange().map(it -> it.begin).map(it -> it.column).orElse(-1);
        var loc = n.findCompilationUnit()
                .flatMap(it -> it.getStorage()).map(it -> it.getPath().toUri()).orElse(null);
        BuildingIssue problem =
                new BuildingIssue("Unsupported element detected given by Java Parser: "
                        + n.getMetaModel().getTypeName() + ". Please extend the KeY-Java-Hierarchy",
                        null, false, line, posInLine, -1, -1, loc);
        throw new BuildingExceptions(Collections.singletonList(problem));
    }

    @Override
    public ModelElement visit(AnnotationDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(AnnotationMemberDeclaration n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ArrayAccessExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ArrayCreationExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ArrayInitializerExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(AssertStmt n, Void arg) {
        Expression cond = (Expression) accept(n.getCheck());
        Expression message = (Expression) accepto(n.getMessage());
        return new Assert(cond, message, createPositionInfo(n));
    }


    @Override
    public ModelElement visit(AssignExpr n, Void arg) {
        var children = visitChildren(n);
        switch (n.getOperator()) {
            case ASSIGN:
                return new CopyAssignment(children);
            case PLUS:
                return new PlusAssignment(children);
            case MINUS:
                return new MinusAssignment(children);
            case MULTIPLY:
                return new TimesAssignment(children);
            case DIVIDE:
                return new DivideAssignment(children);
            case BINARY_AND:
                return new BinaryAndAssignment(children);
            case BINARY_OR:
                return new BinaryOrAssignment(children);
            case XOR:
                return new BinaryXOrAssignment(children);
            case REMAINDER:
                return new ModuloAssignment(children);
            case LEFT_SHIFT:
                return new ShiftLeftAssignment(children);
            case SIGNED_RIGHT_SHIFT:
                return new UnsignedShiftRightAssignment(children);
            case UNSIGNED_RIGHT_SHIFT:
                return new ShiftRightAssignment(children);
        }
        return null;
    }

    @Override
    public ModelElement visit(BinaryExpr n, Void arg) {
        var children = visitChildren(n);
        switch (n.getOperator()) {
            case OR:
                return new LogicalOr(children);
            case AND:
                return new LogicalAnd(children);
            case BINARY_OR:
                return new BinaryOr(children);
            case BINARY_AND:
                return new BinaryAnd(children);
            case XOR:
                return new BinaryXOr(children);
            case EQUALS:
                return new Equals(children);
            case NOT_EQUALS:
                return new NotEquals(children);
            case LESS:
                return new LessThan(children);
            case GREATER:
                return new GreaterThan(children);
            case LESS_EQUALS:
                return new LessOrEquals(children);
            case GREATER_EQUALS:
                return new GreaterOrEquals(children);
            case LEFT_SHIFT:
                return new ShiftLeft(children);
            case SIGNED_RIGHT_SHIFT:
                return new ShiftRight(children);
            case UNSIGNED_RIGHT_SHIFT:
                return new UnsignedShiftRight(children);
            case PLUS:
                return new Plus(children);
            case MINUS:
                return new Minus(children);
            case MULTIPLY:
                return new Times(children);
            case DIVIDE:
                return new Divide(children);
            case REMAINDER:
                return new Modulo(children);
        }
        return null;
    }

    @Override
    public ModelElement visit(BlockStmt n, Void arg) {
        var children = visitChildren(n);
        return new StatementBlock(children);
    }

    @Override
    public ModelElement visit(BooleanLiteralExpr n, Void arg) {
        var children = visitChildren(n);
        return new BooleanLiteral(children, n.getValue());
    }

    @Override
    public ModelElement visit(BreakStmt n, Void arg) {
        var children = visitChildren(n);
        return new Break(children);
    }

    @Override
    public ModelElement visit(CastExpr n, Void arg) {
        var children = visitChildren(n);
        return new TypeCast(children);
    }

    @Override
    public ModelElement visit(CatchClause n, Void arg) {
        var children = visitChildren(n);
        return new Catch(children);
    }

    @Override
    public ModelElement visit(CharLiteralExpr n, Void arg) {
        var children = visitChildren(n);
        return new CharLiteral(children, n.getValue());
    }

    @Override
    public ModelElement visit(ClassExpr n, Void arg) {
        reportUnsupportedElement(n);
        return null;
    }

    @Override
    public ModelElement visit(ClassOrInterfaceDeclaration n, Void arg) {
        var seq = visitChildren(n);
        ProgramElementName fullName = new ProgramElementName(n.getNameAsString());
        boolean isLibrary = false; //TODO weigl
        if (n.isInterface()) {
            return new InterfaceDeclaration(seq, fullName, isLibrary);
        } else {
            return new ClassDeclaration(seq, fullName, isLibrary, n.isInnerClass(), false, n.isLocalClassDeclaration());
        }
    }

    private ExtList visitChildren(Node node) {
        ExtList seq = new ExtList(node.getChildNodes().size());
        for (Node childNode : node.getChildNodes()) {
            var element = childNode.accept(this, null);
            if (element != null) {
                seq.add(element);
            }
        }
        seq.add(createPositionInfo(node));
        return seq;
    }


    private ModelElement accept(Node check) {
        var a = check.accept(this, null);
        mapping.put(check, a);
        return a;
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
    public ModelElement visit(ClassOrInterfaceType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(com.github.javaparser.ast.CompilationUnit n, Void arg) {
        return new CompilationUnit((PackageSpecification) accepto(n.getPackageDeclaration()),
                accepta(n.getImports()), accepta(n.getTypes()));
    }

    private <T> T[] accepta(NodeList<? extends Visitable> nodes) {
        return (T[]) nodes.stream().map(it -> (T) it.accept(this, null)).toArray();
    }

    @Nullable
    private ModelElement accepto(Optional<? extends Visitable> node) {
        if (node.isEmpty()) return null;
        return node.get().accept(this, null);
    }

    @Override
    public ModelElement visit(ConditionalExpr n, Void arg) {
        var children = visitChildren(n);
        return new Conditional(children);
    }

    @Override
    public ModelElement visit(ConstructorDeclaration n, Void arg) {
        boolean parentIsInterface = false;
        var children = visitChildren(n);
        return new de.uka.ilkd.key.java.declaration.ConstructorDeclaration(children, parentIsInterface);
    }

    @Override
    public ModelElement visit(ContinueStmt n, Void arg) {
        var children = visitChildren(n);
        return new Continue(children);
    }

    @Override
    public ModelElement visit(DoStmt n, Void arg) {
        var guard = accept(n.getCondition());
        var body = accept(n.getBody());
        return new Do((Expression) guard, (Statement) body, createPositionInfo(n));
    }

    @Override
    public ModelElement visit(DoubleLiteralExpr n, Void arg) {
        var children = visitChildren(n);
        return new DoubleLiteral(children, n.getValue());
    }

    @Override
    public ModelElement visit(EmptyStmt n, Void arg) {
        var children = visitChildren(n);
        return new EmptyStatement(children);
    }

    @Override
    public ModelElement visit(EnclosedExpr n, Void arg) {
        var children = visitChildren(n);
        return new ParenthesizedExpression(children);
    }

    @Override
    public ModelElement visit(EnumConstantDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(EnumDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ExplicitConstructorInvocationStmt n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ExpressionStmt n, Void arg) {
        var seq = visitChildren(n);
        return (ModelElement) seq.get(0);
    }

    @Override
    public ModelElement visit(FieldAccessExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(FieldDeclaration n, Void arg) {
        var children = visitChildren(n);
        boolean parentIsInferface = false;
        return new de.uka.ilkd.key.java.declaration.FieldDeclaration(children, parentIsInferface);
    }

    @Override
    public ModelElement visit(ForEachStmt n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ForStmt n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(IfStmt n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(InitializerDeclaration n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(InstanceOfExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(IntegerLiteralExpr n, Void arg) {
        var children = visitChildren(n);
        return new IntLiteral(children, n.getValue());
    }

    @Override
    public ModelElement visit(JavadocComment n, Void arg) {
        reportUnsupportedElement(n);
        return null;
    }

    @Override
    public ModelElement visit(LabeledStmt n, Void arg) {
        var id = accept(n.getLabel());
        var stmt = accept(n.getStatement());
        return new LabeledStatement((Label) id, (Statement) stmt, createPositionInfo(n));
    }

    @Override
    public ModelElement visit(LongLiteralExpr n, Void arg) {
        return new LongLiteral(n.getValue());
    }

    @Override
    public ModelElement visit(MarkerAnnotationExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(MemberValuePair n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(MethodCallExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(MethodDeclaration n, Void arg) {
        return new de.uka.ilkd.key.java.declaration.MethodDeclaration(visitChildren(n), false, new Comment[0]);
    }

    @Override
    public ModelElement visit(NameExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(NormalAnnotationExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(NullLiteralExpr n, Void arg) {
        return NullLiteral.NULL;
    }

    @Override
    public ModelElement visit(ObjectCreationExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(PackageDeclaration n, Void arg) {
        if (n.getAnnotations().isNonEmpty()) reportUnsupportedElement(n);

        ProgramElementName name = translateName(n.getName());
        ReferencePrefix prefix = null;//TODO
        return new PackageSpecification(new PackageReference(name, prefix));
    }

    private ProgramElementName translateName(Name name) {
        return new ProgramElementName(name.asString());
    }

    @Override
    public ModelElement visit(Parameter n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(PrimitiveType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(Name n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(SimpleName n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ArrayType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ArrayCreationLevel n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(IntersectionType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(UnionType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ReturnStmt n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(SingleMemberAnnotationExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(StringLiteralExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(SuperExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(SwitchEntry n, Void arg) {
        n.getLabels();
        n.getStatements();
        n.getType();
        //TODO return new Case(e, body);
        return null;
    }

    @Override
    public ModelElement visit(SwitchStmt n, Void arg) {
        return new Switch(visitChildren(n));
    }

    @Override
    public ModelElement visit(SynchronizedStmt n, Void arg) {
        return new Synchronized(visitChildren(n));
    }

    @Override
    public ModelElement visit(ThisExpr n, Void arg) {
        return new ThisReference(visitChildren(n));
    }

    @Override
    public ModelElement visit(ThrowStmt n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(TryStmt n, Void arg) {
        return new Try(visitChildren(n));
    }

    @Override
    public ModelElement visit(LocalClassDeclarationStmt n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(LocalRecordDeclarationStmt n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(TypeParameter n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(UnaryExpr n, Void arg) {
        var c = visitChildren(n);
        switch (n.getOperator()) {
            case PLUS:
                return new Positive(c);
            case MINUS:
                return new Negative(c);
            case PREFIX_INCREMENT:
                return new PreIncrement(c);
            case PREFIX_DECREMENT:
                return new PreDecrement(c);
            case LOGICAL_COMPLEMENT:
                return new LogicalNot(c);
            case BITWISE_COMPLEMENT:
                return new BinaryNot(c);
            case POSTFIX_INCREMENT:
                return new PostIncrement(c);
            case POSTFIX_DECREMENT:
                return new PostDecrement(c);
        }
        return null;
    }

    @Override
    public ModelElement visit(UnknownType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(VariableDeclarationExpr n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(VariableDeclarator n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(VoidType n, Void arg) {
        return null; /*TODO*/
    }

    @Override
    public ModelElement visit(WhileStmt n, Void arg) {
        return new While(/*TODO*/);
    }

    @Override
    public ModelElement visit(WildcardType n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(LambdaExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(MethodReferenceExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(TypeExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ImportDeclaration n, Void arg) {
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
    public ModelElement visit(ModuleDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ModuleRequiresDirective n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ModuleExportsDirective n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ModuleProvidesDirective n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ModuleUsesDirective n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ModuleOpensDirective n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(UnparsableStmt n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(ReceiverParameter n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(VarType n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(Modifier n, Void arg) {
        ExtList children = visitChildren(n);
        var k = n.getKeyword();
        switch (k) {
            case DEFAULT:
                reportUnsupportedElement(n);
                break;
            case PUBLIC:
                return new Public(children);
            case PROTECTED:
                return new Protected(children);
            case PRIVATE:
                return new Private(children);
            case ABSTRACT:
                return new Abstract(children);
            case STATIC:
                return new Static(children);
            case FINAL:
                return new Final(children);
            case TRANSIENT:
                return new Transient(children);
            case VOLATILE:
                return new Volatile(children);
            case SYNCHRONIZED:
                return new Synchronized(children);
            case NATIVE:
                return new Native(children);
            case STRICTFP:
                return new StrictFp(children);
            case TRANSITIVE:
                reportUnsupportedElement(n);
                break;
            case GHOST:
                return new Ghost(children);
            case MODEL:
                return new Model(children);
            case TWO_STATE:
                return new TwoState(children);
            case NO_STATE:
                return new NoState(children);
        }
        return null;
    }

    @Override
    public ModelElement visit(SwitchExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(YieldStmt n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(TextBlockLiteralExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(PatternExpr n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(RecordDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(CompactConstructorDeclaration n, Void arg) {
        reportUnsupportedElement(n);
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyCcatchBreak n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyCcatchContinue n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyCcatchParameter n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyCcatchReturn n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyCatchAllStatement n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyEscapeExpression n, Void arg) {
        //return new EscapeExpression(visitChildren(n));
        return null;
    }

    @Override
    public ModelElement visit(KeyExecStatement n, Void arg) {
        return new Exec(visitChildren(n));
    }

    @Override
    public ModelElement visit(KeyExecutionContext n, Void arg) {
        return new ExecutionContext(visitChildren(n));
    }

    @Override
    public ModelElement visit(KeyLoopScopeBlock n, Void arg) {
        return new LoopScopeBlock(visitChildren(n));
    }

    @Override
    public ModelElement visit(KeyMergePointStatement n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyMethodBodyStatement n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyMethodCallStatement n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyMethodSignature n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyRangeExpression n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyTransactionStatement n, Void arg) {
        return new TransactionStatement(n.getType().ordinal());
    }

    @Override
    public ModelElement visit(KeyContextStatementBlock n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyExecCtxtSV n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyExpressionSV n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyJumpLabelSV n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyMetaConstructExpression n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyMetaConstruct n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyMetaConstructType n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyMethodSignatureSV n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyPassiveExpression n, Void arg) {
        return new PassiveExpression(visitChildren(n));
    }

    @Override
    public ModelElement visit(KeyProgramVariableSV n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyStatementSV n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyTypeSV n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyCcatchSV n, Void arg) {
        return super.visit(n, arg);
    }

    @Override
    public ModelElement visit(KeyExecutionContextSV n, Void arg) {
        return super.visit(n, arg);
    }
}