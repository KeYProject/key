// Imports are copied to every file
import org.jspecify.annotations.Nullable;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.java.ast.PositionInfo;

// ROOT
abstract class JavaSourceElement {
    @EqEx @Nullable PositionInfo positionInfo;
}

class CompilationUnit extends JavaNonTerminalProgramElement {
    @Nullable PackageSpecification packageSpec;
    List<Import> imports;
    List<TypeDeclaration> typeDeclarations;
}

class ContextStatementBlock extends StatementBlock { }

abstract class Declaration { }

abstract class ExpressionContainer { }

class Import extends JavaNonTerminalProgramElement {
    boolean isMultiImport;
    TypeReferenceInfix reference;
}

abstract class JavaNonTerminalProgramElement extends JavaProgramElement {}

abstract class JavaProgramElement extends JavaSourceElement {}

abstract class Label {}

abstract class LoopInitializer {}

abstract class NamedProgramElement {}

class PackageSpecification extends JavaNonTerminalProgramElement {

    PackageReference reference;
}

abstract class ParameterContainer {}

abstract class ProgramElement {}

abstract class ProgramVariableName {}

abstract class Reference {}

abstract class ScopeDefiningElement {}

abstract class Statement {}

class StatementBlock extends JavaStatement {}

abstract class StatementContainer {}

abstract class TerminalProgramElement {}

abstract class TypeScope {}

abstract class VariableScope {}

class CcatchBreakLabelParameterDeclaration extends CcatchNonstandardParameterDeclaration {}

class CcatchBreakWildcardParameterDeclaration extends CcatchNonstandardParameterDeclaration {}

class CcatchContinueLabelParameterDeclaration extends CcatchNonstandardParameterDeclaration {}

class CcatchContinueParameterDeclaration extends CcatchNonstandardParameterDeclaration {}

class CcatchContinueWildcardParameterDeclaration extends CcatchNonstandardParameterDeclaration {}

abstract class CcatchNonstandardParameterDeclaration extends JavaNonTerminalProgramElement {}

class CcatchReturnParameterDeclaration extends CcatchNonstandardParameterDeclaration {}

class CcatchReturnValParameterDeclaration extends CcatchNonstandardParameterDeclaration {}

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

class FieldSpecification extends VariableSpecification {}

class Implements extends InheritanceSpecification {}

abstract class InheritanceSpecification extends JavaNonTerminalProgramElement {

    List<TypeReference> supertypes;
}

class InterfaceDeclaration extends TypeDeclaration {

    Extends extending;
}

abstract class JavaDeclaration extends JavaNonTerminalProgramElement {

    ImmutableList<de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct> attachedJml;

    List<Modifier> modArray;
}

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

class SuperArrayDeclaration extends TypeDeclaration {}

class Throws extends JavaNonTerminalProgramElement {

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

class VariableSpecification extends JavaNonTerminalProgramElement {

    Expression initializer;

    int dimensions;

    Type type;

    IProgramVariable programVariable;
}

class AnnotationUseSpecification extends Modifier {

    TypeReference tr;
}


class ArrayInitializer extends JavaNonTerminalProgramElement {
    KeYJavaType kjt;
}
abstract class Expression {}

abstract class ExpressionStatement {}

abstract class Operator extends JavaNonTerminalProgramElement {}

class ParenthesizedExpression extends Operator {
    Expression child;
}

class PassiveExpression extends Operator{
    Expression child;
}

abstract class Literal extends JavaProgramElement {
    String value;
}

abstract class AbstractIntegerLiteral extends Literal {
}

class BooleanLiteral extends Literal {}

class CharLiteral extends AbstractIntegerLiteral {}

class DoubleLiteral extends Literal {}

class EmptyMapLiteral extends Literal {}

class EmptySeqLiteral extends Literal {}

class EmptySetLiteral extends Literal {}

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


class ArrayLengthReference extends JavaNonTerminalProgramElement {

    ReferencePrefix prefix;
}

class ArrayReference extends JavaNonTerminalProgramElement {

    ReferencePrefix prefix;

    List<Expression> inits;
}

abstract class ConstructorReference {}

class ExecutionContext extends JavaNonTerminalProgramElement {

    TypeReference classContext;

    ReferencePrefix runtimeInstance;
}

class FieldReference extends VariableReference {

    ReferencePrefix prefix;
}

abstract class IExecutionContext {}

abstract class MemberReference {}

class MetaClassReference extends JavaNonTerminalProgramElement {

    TypeReference typeReference;
}

abstract class MethodName {}

abstract class MethodOrConstructorReference {}

class MethodReference extends JavaNonTerminalProgramElement {

    ReferencePrefix prefix;

    MethodName name;

    List<? extends Expression> arguments;
}

abstract class NameReference {}

class PackageReference extends JavaNonTerminalProgramElement {

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

abstract class SpecialConstructorReference extends JavaNonTerminalProgramElement {

    List<Expression> arguments;
}

class SuperConstructorReference extends SpecialConstructorReference {

    ReferencePrefix prefix;
}

class SuperReference extends JavaNonTerminalProgramElement {}

class ThisConstructorReference extends SpecialConstructorReference {}

class ThisReference extends JavaNonTerminalProgramElement {}

class TypeRef extends TypeReferenceImp {}

abstract class TypeReference {}

abstract class TypeReferenceContainer {}

abstract class TypeReferenceImp extends JavaNonTerminalProgramElement {

    ReferencePrefix prefix;

    int dimensions;

    ProgramElementName name;
}

abstract class TypeReferenceInfix {}

class VariableReference extends JavaNonTerminalProgramElement {

    ProgramVariable variable;
}

class Assert extends JavaStatement {
    Expression expression;
    @Nullable String message;
}

abstract class Branch {}

abstract class BranchStatement extends JavaStatement {}

class Break extends LabelJumpStatement {}

class Case extends Branch {
    Expression expression;
    List<Statement> body;
}

class Default extends Branch {
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

class Else extends BranchImp {

    Statement body;
}

class EmptyStatement extends JavaProgramElement {}

class EnhancedFor extends LoopStatement {}

class Exec extends BranchStatement {}

abstract class ExpressionJumpStatement extends JumpStatement {
    Expression expression;
}

class Finally extends BranchImp {

    StatementBlock body;
}

class For extends LoopStatement {}

class ForUpdates extends JavaNonTerminalProgramElement {

    List<Expression> updates;
}

class Guard extends JavaNonTerminalProgramElement {

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

abstract class JavaStatement extends JavaNonTerminalProgramElement {}

class JmlAssert extends JavaStatement {}

abstract class JumpStatement extends JavaStatement {}

abstract class LabelJumpStatement extends JumpStatement {
    Label name;
}

class LabeledStatement extends JavaStatement {
    Label name;
    Statement body;
}

class LoopInit extends JavaNonTerminalProgramElement {
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

class MethodBodyStatement extends JavaNonTerminalProgramElement {}

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

class Then extends BranchImp {}

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

class InitArrayCreation extends InitArray {}

abstract class ProgramTransformer extends JavaNonTerminalProgramElement {}
class ReattachLoopInvariant extends ProgramTransformer {}
class SpecialConstructorCall extends ProgramTransformer {}
class StaticInitialisation extends ProgramTransformer {}
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
class ForToWhile extends ProgramTransformer {}
abstract class InitArray extends ProgramTransformer {}
