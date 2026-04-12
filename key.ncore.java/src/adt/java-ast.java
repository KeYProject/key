// Imports are copied to every file
import org.jspecify.annotations.Nullable;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import org.key_project.logic.op.sv.*;

@Root
abstract class JavaSourceElement implements Visitable, Matchable {
    @EqEx @Nullable PositionInfo positionInfo;
}

class CompilationUnit extends JavaProgramElement {
    @Nullable PackageReference packageReference;
    List<Import> imports;
    List<TypeDeclaration> typeDeclarations;
}

class ContextStatementBlock extends StatementBlock {
    IExecutionContext executionContext;
}

abstract class Declaration {
    List<Modifier> getModifiers();
}

abstract class ExpressionContainer {}

class Import extends JavaProgramElement {
    boolean isMultiImport;
    boolean isStatic;
    TypeReferenceInfix reference;
}

abstract class Label {}

abstract class LoopInitializer {}

abstract class NamedProgramElement {}

abstract class ParameterContainer {}

abstract class ProgramElement {}

abstract class ProgramVariableName {}

abstract class Reference {}

abstract class ScopeDefiningElement {}

abstract class Statement {}

class StatementBlock extends JavaStatement {
    List<Statement> statement;
    @Nullable MethodFrame innerMostMethodFrame;
}

abstract class CcatchNonstandardParameterDeclaration extends JavaProgramElement {
    ParameterDeclaration delegate;
    boolean isWildcard;
    boolean isBreak;
    boolean isContinue;
    boolean isReturn;
}

class ArrayDeclaration extends TypeDeclaration {}

class ClassDeclaration extends TypeDeclaration {

    Extends extending;

    Implements implementing;

    boolean isInnerClass;

    boolean isLocalClass;

    boolean isAnonymousClass;
}

class ClassInitializer extends JavaDeclaration {

    StatementBlock body;
}

class ConstructorDeclaration extends MethodDeclaration {}

class EnumClassDeclaration extends ClassDeclaration {}

class Extends extends InheritanceSpecification {}

class FieldDeclaration extends VariableDeclaration {

    List<FieldSpecification> fieldSpecs;
}

class FieldSpecification extends VariableSpecification {
    Type type;
    int dimensions;
    ProgramVariable var;
    @Nullable Expression init;
}

class Implements extends InheritanceSpecification {
    List<TypeReference> typeRefs;
}

abstract class InheritanceSpecification extends JavaProgramElement {
    List<TypeReference> supertypes;
}

class InterfaceDeclaration extends TypeDeclaration {
    List<TypeReference> extending;
}

abstract class JavaDeclaration extends Declaration { }

class LocalVariableDeclaration extends VariableDeclaration {
    List<VariableSpecification> varSpecs;
}

abstract class MemberDeclaration {}

class MethodDeclaration extends JavaDeclaration {
    TypeReference returnType;
    Comment[] voidComments;
    ProgramElementName name;
    List<ParameterDeclaration> parameters;
    Throws exceptions;
    StatementBlock body;
    JMLModifiers jmlModifiers;
    boolean parentIsInterfaceDeclaration;
}

abstract class Modifier extends JavaProgramElement {}

class ParameterDeclaration extends VariableDeclaration {
    List<VariableSpecification> varSpec;
}

class SuperArrayDeclaration extends TypeDeclaration {
    ProgramElementName name;
    FieldDeclaration length;
}

class Throws extends JavaProgramElement {
    List<TypeReference> exceptions;
}

abstract class TypeDeclaration extends JavaDeclaration {
    ProgramElementName name;
    ProgramElementName fullName;
    List<MemberDeclaration> members;
    boolean parentIsInterfaceDeclaration;
    boolean isLibrary;
    JMLModifiers jmlModifiers;
}

abstract class TypeDeclarationContainer {}

abstract class VariableDeclaration extends JavaDeclaration {
    TypeReference typeReference;
    boolean parentIsInterfaceDeclaration;
}

class VariableSpecification extends JavaProgramElement {
    Expression initializer;
    int dimensions;
    Type type;
    IProgramVariable programVariable;
}

class AnnotationUseSpecification extends Modifier {
    TypeReference tr;
}


class ArrayInitializer extends JavaProgramElement {
    KeYJavaType kjt;
}

abstract class ExpressionStatement {}

//region expressions
abstract class Expression {
    public KeYJavaType getType(Services services) {
        return accept(new FindReturnType());
    }
}

class ParenthesizedExpression extends Expression{
    Expression child;
}

class PassiveExpression extends Expression {
    Expression child;
}

abstract class Literal extends Expression {
    String value;
}

class BooleanLiteral extends Literal {
}

class DoubleLiteral extends Literal {}
class FloatLiteral extends Literal {
    String value;
}

class FreeLiteral extends Literal {}

class IntLiteral extends AbstractIntegerLiteral {}

class LongLiteral extends AbstractIntegerLiteral {}

class RealLiteral extends Literal {}

class StringLiteral extends Literal {}

class Assignment extends Operator {
    AssignmentKind kind;
    Expression left;
    Expression right;
}


class BinaryOperator extends Operator {
    BinaryOperatorKind kind;
    Expression left;
    Expression right;
}

class UnaryOperator implements Operator {
    UnaryOperatorKind kind;
    Expression child;

}

class LogicalFunctionOperator extends Operator {
    LogicFunction function;
    List<Expression> arguments;
}

class Conditional extends Operator {
    Expression condition;
    Expression thenExpr;
    Expression elseExpr;
}

class DLEmbeddedExpression extends Operator {}

class ExactInstanceof extends TypeOperator {}

class Instanceof extends TypeOperator {}

class New extends TypeOperator {

    ClassDeclaration anonymousClass;

    ReferencePrefix accessPath;
}

class NewArray extends TypeOperator {

    int dimensions;

    ArrayInitializer arrayInitializer;
}

class TypeCast extends TypeOperator {}

abstract class TypeOperator extends Operator {

    TypeReference typeReference;
}


class ArrayLengthReference extends JavaProgramElement {

    ReferencePrefix prefix;
}

class ArrayReference extends JavaProgramElement {

    ReferencePrefix prefix;

    List<Expression> inits;
}

abstract class ConstructorReference {}

class ExecutionContext extends JavaProgramElement {

    TypeReference classContext;

    ReferencePrefix runtimeInstance;
}

class FieldReference extends VariableReference {

    ReferencePrefix prefix;
}

abstract class IExecutionContext {}

abstract class MemberReference {}

class MetaClassReference extends JavaProgramElement {

    TypeReference typeReference;
}

abstract class MethodName {}

abstract class MethodOrConstructorReference {}

class MethodReference extends JavaProgramElement {

    ReferencePrefix prefix;

    MethodName name;

    List<? extends Expression> arguments;
}

abstract class NameReference {}

class PackageReference extends JavaProgramElement {

    ReferencePrefix prefix;

    ProgramElementName name;
}

abstract class PackageReferenceContainer {}

abstract class ReferencePrefix {}

abstract class ReferenceSuffix {}

class SchemaTypeReference extends TypeReferenceImp {}

class SchematicFieldReference extends FieldReference {

    SchemaVariable schemaVariable;
}

abstract class SpecialConstructorReference extends JavaProgramElement {

    List<Expression> arguments;
}

class SuperConstructorReference extends SpecialConstructorReference {

    ReferencePrefix prefix;
}

class SuperReference extends JavaProgramElement {}

class ThisConstructorReference extends SpecialConstructorReference {}

class ThisReference extends JavaProgramElement {}

class TypeRef extends TypeReferenceImp {}

abstract class TypeReference {}

abstract class TypeReferenceContainer {}

abstract class TypeReferenceImp extends JavaProgramElement {

    ReferencePrefix prefix;

    int dimensions;

    ProgramElementName name;
}

abstract class TypeReferenceInfix {}

class VariableReference extends JavaProgramElement {

    ProgramVariable variable;
}

class Assert extends JavaStatement {
    Expression expression;
    @Nullable String message;
}

abstract class BranchStatement extends JavaStatement {}

class Break extends LabelJumpStatement {}

class Case {
    Expression expression;
    List<Statement> body;
}

class Default {
    List<Statement> body;
}

abstract class CatchClause {}

class SingleCatch {
    ParameterDeclaration parameter;
    StatementBlock body;
}

class CatchAllStatement extends CatchClause {}
class Ccatch extends CatchClause {}

class Continue extends LabelJumpStatement {}

class Do extends LoopStatement {}

class EmptyStatement extends JavaProgramElement {}

class EnhancedFor extends LoopStatement {}

class Exec extends BranchStatement {}

abstract class ExpressionJumpStatement extends JumpStatement {
    Expression expression;
}

class For extends LoopStatement {}

class ForUpdates extends JavaProgramElement {

    List<Expression> updates;
}

class Guard extends JavaProgramElement {

    Expression expr;
}

abstract class IForUpdates {}
abstract class IGuard {}
abstract class ILoopInit {}

class If extends BranchStatement {
    Expression condition;
    Statement thenBranch;
    Statement elseBranch;
}

abstract class JavaStatement extends JavaProgramElement {}

class JmlAssert extends JavaStatement {}

abstract class JumpStatement extends JavaStatement {}

abstract class LabelJumpStatement extends JumpStatement {
    Label name;
}

class LabeledStatement extends JavaStatement {
    Label name;
    Statement body;
}

class LoopInit extends JavaProgramElement {
    List<LoopInitializer> inits;
}

class LoopScopeBlock extends JavaStatement {
    Expression variant;
    Statement body;
}

abstract class LoopStatement extends JavaStatement {
    ILoopInit inits;
    IForUpdates updates;
    IGuard guard;
    Statement body;
    ImmutableList<TextualJMLConstruct> attachedJml;
}

class MergePointStatement extends JavaStatement {

    IProgramVariable identifier;
}

class MethodBodyStatement extends JavaProgramElement {}

class MethodFrame extends JavaStatement {}

class Return extends ExpressionJumpStatement {}

class SetStatement extends JavaStatement {}

class Switch extends BranchStatement {
    Expression expression;
    List<Branch> branches;
}

class SynchronizedBlock extends JavaStatement {

    Expression expression;

    StatementBlock body;
}

class Throw extends ExpressionJumpStatement {}

class TransactionStatement extends JavaStatement {}

class Try extends BranchStatement {
    StatementBlock tryBlock;
    List<Catch> catches;
    @Nullable StatementBlock finallyBlock;
}

class While extends LoopStatement {}

abstract class ProgramConstruct {}

class ProgramElementName extends Name {}

abstract class ProgramPrefix {}

abstract class IndProgramElementName extends ProgramElementName {}

class PermIndProgramElementName extends IndProgramElementName {}

class TempIndProgramElementName extends IndProgramElementName {}

abstract class IProgramMethod {}
abstract class IProgramVariable {}

class LocationVariable extends ProgramVariable {}
class ProgramConstant extends ProgramVariable {}
class ProgramMethod extends ObserverFunction {}

class ProgramSV extends JOperatorSV {}

abstract class ProgramVariable extends JAbstractSortedOperator {}

abstract class AbstractProgramElement {}

abstract class ProgramTransformer extends JavaProgramElement {
    /** the name of the meta construct */
    String name;
    /** the encapsulated program element */
    ProgramElement body;
}

class ReattachLoopInvariant extends ProgramTransformer {
    String name = "#reattachLoopInvariant";
    LoopStatment body;
}

class SpecialConstructorCall extends ProgramTransformer {
    String name = "special-constructor-call";
}

class StaticInitialisation extends ProgramTransformer {
    String name = "static-initialisation";
    Expression body;
}

class SwitchToIf extends ProgramTransformer {}
class TypeOf extends ProgramTransformer {}
class Unpack extends ProgramTransformer {}
class UnwindLoop extends ProgramTransformer {}
class MultipleVarDecl extends ProgramTransformer {}
class PostWork extends ProgramTransformer {}
class IsStatic extends ProgramTransformer {}
class MethodCall extends ProgramTransformer {
    MethodReference methRef;
    ReferencePrefix newContext;
    ProgramVariable pvar;
    List<Expression> arguments;
    KeYJavaType staticPrefixType;
}
class ArrayLength extends ProgramTransformer {}
class ArrayPostDecl extends ProgramTransformer {}
class ConstructorCall extends ProgramTransformer {}
class CreateObject extends ProgramTransformer {}
class DoBreak extends ProgramTransformer {}
class EnhancedForElimination extends ProgramTransformer {}
class EvaluateArgs extends ProgramTransformer {}
class ExpandMethodBody extends ProgramTransformer {}
class ForInitUnfoldTransformer extends ProgramTransformer {}

/**
 * converts a for-loop to a while loop. Invariant and other rules cannot be performed on for but
 * only on while loops.
 *
 * It makes uses of the {@link ForToWhileTransformation} to create a transformed loop body which is
 * then put into the corresponding context.
 *
 * <h2>Example</h2>
 *
 * <pre>
 * for (int i = 0; i &lt; 100; i++) {
 *     if (i == 2)
 *         continue;
 *     if (i == 3)
 *         break;
 * }
 * </pre>
 *
 * is translated to
 *
 * <pre>
 * _label1: {
 *     int i = 0;
 *     while (i &lt; 100) {
 *         _label0: {
 *             if (i == 2)
 *                 break _label0;
 *             if (i == 3)
 *                 break _label1;
 *         }
 *         i++;
 *     }
 * }
 * </pre>
 *
 * @see ForToWhileTransformation
 * @author MU
 */
class ForToWhile extends ProgramTransformer {
    SchemaVariable innerLabel;
    SchemaVariable outerLabel;
    Statement body;
    String name = "#for-to-while";
}

abstract class InitArray extends ProgramTransformer {}
class InitArrayCreation extends InitArray {
    SchemaVariable newObjectSV;
    ProgramElement body;
    String name = "init-array-creation";
}

