import org.jspecify.annotations.Nullable;

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

abstract class JavaNonTerminalProgramElement extends JavaProgramElement {
}

abstract class JavaProgramElement extends JavaSourceElement {
}

abstract class Label {
}

abstract class LoopInitializer {
}

abstract class NamedProgramElement {
}

class PackageSpecification extends JavaNonTerminalProgramElement {

    PackageReference reference;
}

abstract class ParameterContainer {
}

abstract class ProgramElement {
}

abstract class ProgramVariableName {
}

abstract class Reference {
}

abstract class ScopeDefiningElement {
}

abstract class Statement {
}

class StatementBlock extends JavaStatement {
}

abstract class StatementContainer {
}

abstract class TerminalProgramElement {
}

abstract class TypeScope {
}

abstract class VariableScope {
}

class CcatchBreakLabelParameterDeclaration extends CcatchNonstandardParameterDeclaration {
}

class CcatchBreakWildcardParameterDeclaration extends CcatchNonstandardParameterDeclaration {
}

class CcatchContinueLabelParameterDeclaration extends CcatchNonstandardParameterDeclaration {
}

class CcatchContinueParameterDeclaration extends CcatchNonstandardParameterDeclaration {
}

class CcatchContinueWildcardParameterDeclaration extends CcatchNonstandardParameterDeclaration {
}

abstract class CcatchNonstandardParameterDeclaration extends JavaNonTerminalProgramElement {
}

class CcatchReturnParameterDeclaration extends CcatchNonstandardParameterDeclaration {
}

class CcatchReturnValParameterDeclaration extends CcatchNonstandardParameterDeclaration {
}

class ArrayDeclaration extends TypeDeclaration {
}

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

class ConstructorDeclaration extends MethodDeclaration {
}

class EnumClassDeclaration extends ClassDeclaration {
}

class Extends extends InheritanceSpecification {
}

class FieldDeclaration extends VariableDeclaration {

    List<FieldSpecification> fieldSpecs;
}

class FieldSpecification extends VariableSpecification {
}

class Implements extends InheritanceSpecification {
}

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

abstract class MemberDeclaration {
}

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

abstract class Modifier extends JavaProgramElement {
}

class ParameterDeclaration extends VariableDeclaration {
    List<VariableSpecification> varSpec;
}

class SuperArrayDeclaration extends TypeDeclaration {
}

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

abstract class TypeDeclarationContainer {
}

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

class Abstract extends Modifier {
}

class AnnotationUseSpecification extends Modifier {

    TypeReference tr;
}

class Final extends Modifier {
}

class Ghost extends Modifier {
}

class Model extends Modifier {
}

class ABSTRACT extends Modifier {
}

class DEFAULT extends Modifier {
}

class FINAL extends Modifier {
}

class JML_CODE extends Modifier {
}

class JML_CODE_BIGINT_MATH extends Modifier {
}

class JML_CODE_JAVA_MATH extends Modifier {
}

class JML_CODE_SAFE_MATH extends Modifier {
}

class JML_HELPER extends Modifier {
}

class JML_INSTANCE extends Modifier {
}

class JML_NON_NULL extends Modifier {
}

class JML_NON_NULL_BY_DEFAULT extends Modifier {
}

class JML_NON_NULL_ELEMENTS extends Modifier {
}

class JML_NO_STATE extends Modifier {
}

class JML_NULLABLE extends Modifier {
}

class JML_NULLABLE_BY_DEFAULT extends Modifier {
}

class JML_OT_READ_ONLY extends Modifier {
}

class JML_OT_REP extends Modifier {
}

class JML_PACKAGE extends Modifier {
}

class JML_PURE extends Modifier {
}

class JML_SPEC_BIGINT_MATH extends Modifier {
}

class JML_SPEC_JAVA_MATH extends Modifier {
}

class JML_SPEC_PACKAGE extends Modifier {
}

class JML_SPEC_PRIVATE extends Modifier {
}

class JML_SPEC_PROTECTED extends Modifier {
}

class JML_SPEC_PUBLIC extends Modifier {
}

class JML_SPEC_SAFE_MATH extends Modifier {
}

class JML_STRICTLY_PURE extends Modifier {
}

class JML_TWO_STATE extends Modifier {
}

class JML_UNPARSABLE_MODIFIERS extends Modifier {
}

class NATIVE extends Modifier {
}

class NON_SEALED extends Modifier {
}

class PRIVATE extends Modifier {
}

class PROTECTED extends Modifier {
}

class PUBLIC extends Modifier {
}

class SEALED extends Modifier {
}

class STATIC extends Modifier {
}

class STRICTFP extends Modifier {
}

class SYNCHRONIZED extends Modifier {
}

class TRANSIENT extends Modifier {
}

class TRANSITIVE extends Modifier {
}

class VOLATILE extends Modifier {
}

class Native extends Modifier {
}

class NoState extends Modifier {
}

class Private extends VisibilityModifier {
}

class Protected extends VisibilityModifier {
}

class Public extends VisibilityModifier {
}

class Static extends Modifier {
}

class StrictFp extends Modifier {
}

class Synchronized extends Modifier {
}

class Transient extends Modifier {
}

class TwoState extends Modifier {
}

abstract class VisibilityModifier extends Modifier {
}

class Volatile extends Modifier {}

class ArrayInitializer extends JavaNonTerminalProgramElement {
    KeYJavaType kjt;
}

abstract class Assignment extends Operator {
}

abstract class Expression {
}

abstract class ExpressionStatement {
}

abstract class Operator extends JavaNonTerminalProgramElement {
}

class ParenthesizedExpression extends Operator {}

class PassiveExpression extends ParenthesizedExpression {}

abstract class AbstractIntegerLiteral extends Literal {}

class BooleanLiteral extends Literal {}

class CharLiteral extends AbstractIntegerLiteral {}

class DoubleLiteral extends Literal {

    String value;
}

class EmptyMapLiteral extends Literal {
}

class EmptySeqLiteral extends Literal {
}

class EmptySetLiteral extends Literal {
}

class FloatLiteral extends Literal {

    String value;
}

class FreeLiteral extends Literal {
}

class IntLiteral extends AbstractIntegerLiteral {
}

abstract class Literal extends JavaProgramElement {}

class LongLiteral extends AbstractIntegerLiteral {}

class RealLiteral extends Literal {
    String value;
}

class StringLiteral extends Literal {
    String value;
}

class BinaryAnd extends BinaryOperator {
}

class BinaryAndAssignment extends Assignment {
}

class BinaryNot extends Operator {
}

abstract class BinaryOperator extends Operator {
}

class BinaryOr extends BinaryOperator {
}

class BinaryOrAssignment extends Assignment {
}

class BinaryXOr extends BinaryOperator {
}

class BinaryXOrAssignment extends Assignment {
}

abstract class ComparativeOperator extends Operator {
}

class Conditional extends Operator {
}

class CopyAssignment extends Assignment {
}

class DLEmbeddedExpression extends Operator {
}

class Divide extends BinaryOperator {
}

class DivideAssignment extends Assignment {
}

class Equals extends ComparativeOperator {
}

class ExactInstanceof extends TypeOperator {
}

class GreaterOrEquals extends ComparativeOperator {
}

class GreaterThan extends ComparativeOperator {
}

class Instanceof extends TypeOperator {
}

class Intersect extends BinaryOperator {
}

class LessOrEquals extends ComparativeOperator {
}

class LessThan extends ComparativeOperator {
}

class LogicalAnd extends Operator {
}

class LogicalNot extends Operator {
}

class LogicalOr extends Operator {
}

class Minus extends BinaryOperator {
}

class MinusAssignment extends Assignment {
}

class Modulo extends BinaryOperator {
}

class ModuloAssignment extends Assignment {
}

class Negative extends Operator {
}

class New extends TypeOperator {

    ClassDeclaration anonymousClass;

    ReferencePrefix accessPath;
}

class NewArray extends TypeOperator {

    int dimensions;

    ArrayInitializer arrayInitializer;
}

class NotEquals extends ComparativeOperator {
}

class Plus extends BinaryOperator {
}

class PlusAssignment extends Assignment {
}

class Positive extends Operator {
}

class PostDecrement extends Assignment {
}

class PostIncrement extends Assignment {
}

class PreDecrement extends Assignment {
}

class PreIncrement extends Assignment {
}

class ShiftLeft extends Operator {
}

class ShiftLeftAssignment extends Assignment {
}

class ShiftRight extends Operator {
}

class ShiftRightAssignment extends Assignment {
}

class Subtype extends BinaryOperator {
}

class Times extends BinaryOperator {
}

class TimesAssignment extends Assignment {
}

class TypeCast extends TypeOperator {
}

abstract class TypeOperator extends Operator {

    TypeReference typeReference;
}

class UnsignedShiftRight extends Operator {
}

class UnsignedShiftRightAssignment extends Assignment {
}

class AllFields extends Operator {
}

class AllObjects extends Operator {
}

class SeqConcat extends BinaryOperator {
}

class SeqGet extends Operator {
}

class SeqIndexOf extends Operator {
}

class SeqLength extends Operator {
}

class SeqPut extends Operator {
}

class SeqReverse extends Operator {
}

class SeqSingleton extends Operator {
}

class SeqSub extends Operator {
}

class SetMinus extends BinaryOperator {
}

class SetUnion extends BinaryOperator {
}

class Singleton extends Operator {
}

class ArrayLengthReference extends JavaNonTerminalProgramElement {

    ReferencePrefix prefix;
}

class ArrayReference extends JavaNonTerminalProgramElement {

    ReferencePrefix prefix;

    List<Expression> inits;
}

abstract class ConstructorReference {
}

class ExecutionContext extends JavaNonTerminalProgramElement {

    TypeReference classContext;

    ReferencePrefix runtimeInstance;
}

class FieldReference extends VariableReference {

    ReferencePrefix prefix;
}

abstract class IExecutionContext {
}

abstract class MemberReference {
}

class MetaClassReference extends JavaNonTerminalProgramElement {

    TypeReference typeReference;
}

abstract class MethodName {
}

abstract class MethodOrConstructorReference {
}

class MethodReference extends JavaNonTerminalProgramElement {

    ReferencePrefix prefix;

    MethodName name;

    List<? extends Expression> arguments;
}

abstract class NameReference {
}

class PackageReference extends JavaNonTerminalProgramElement {

    ReferencePrefix prefix;

    ProgramElementName name;
}

abstract class PackageReferenceContainer {
}

abstract class ReferencePrefix {
}

abstract class ReferenceSuffix {
}

class SchemaTypeReference extends TypeReferenceImp {
}

class SchematicFieldReference extends FieldReference {

    SchemaVariable schemaVariable;
}

abstract class SpecialConstructorReference extends JavaNonTerminalProgramElement {

    List<Expression> arguments;
}

class SuperConstructorReference extends SpecialConstructorReference {

    ReferencePrefix prefix;
}

class SuperReference extends JavaNonTerminalProgramElement {
}

class ThisConstructorReference extends SpecialConstructorReference {
}

class ThisReference extends JavaNonTerminalProgramElement {
}

class TypeRef extends TypeReferenceImp {
}

abstract class TypeReference {
}

abstract class TypeReferenceContainer {
}

abstract class TypeReferenceImp extends JavaNonTerminalProgramElement {

    ReferencePrefix prefix;

    int dimensions;

    ProgramElementName name;
}

abstract class TypeReferenceInfix {
}

class VariableReference extends JavaNonTerminalProgramElement {

    ProgramVariable variable;
}

class Assert extends JavaStatement {
}

abstract class Branch {}

abstract class BranchImp extends JavaNonTerminalProgramElement {
}

abstract class BranchStatement extends JavaStatement {}

class Break extends LabelJumpStatement {}

class Case extends BranchImp {
    Expression expression;
    List<Statement> body;
}

class Catch extends BranchImp {
    ParameterDeclaration parameter;
    StatementBlock body;
}

class CatchAllStatement extends JavaNonTerminalProgramElement {}

class Ccatch extends BranchImp {}

class Continue extends LabelJumpStatement {}

class Default extends BranchImp {
    List<Statement> body;
}

class Do extends LoopStatement {
}

class Else extends BranchImp {

    Statement body;
}

class EmptyStatement extends JavaProgramElement {
}

class EnhancedFor extends LoopStatement {
}

class Exec extends BranchStatement {
}

abstract class ExpressionJumpStatement extends JumpStatement {

    Expression expression;
}

class Finally extends BranchImp {

    StatementBlock body;
}

class For extends LoopStatement {
}

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

abstract class JavaStatement extends JavaNonTerminalProgramElement {
}

class JmlAssert extends JavaStatement {
}

abstract class JumpStatement extends JavaStatement {
}

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
}

abstract class LoopStatement extends JavaStatement {

    ILoopInit inits;

    IForUpdates updates;

    IGuard guard;

    Statement body;

    ImmutableList<de.uka.ilkd.key.speclang.jml.pretranslation.TextualJMLConstruct> attachedJml;
}

class MergePointStatement extends JavaStatement {

    IProgramVariable identifier;
}

class MethodBodyStatement extends JavaNonTerminalProgramElement {
}

class MethodFrame extends JavaStatement {
}

class Return extends ExpressionJumpStatement {
}

class SetStatement extends JavaStatement {
}

class Switch extends BranchStatement {

    List<Branch> branches;

    Expression expression;
}

class SynchronizedBlock extends JavaStatement {

    Expression expression;

    StatementBlock body;
}

class Then extends BranchImp {
}

class Throw extends ExpressionJumpStatement {
}

class TransactionStatement extends JavaStatement {
}

class Try extends BranchStatement {
}

class While extends LoopStatement {
}

abstract class ProgramConstruct {
}

class ProgramElementName extends Name {
}

abstract class ProgramPrefix {
}

abstract class IndProgramElementName extends ProgramElementName {
}

class PermIndProgramElementName extends IndProgramElementName {
}

class TempIndProgramElementName extends IndProgramElementName {
}

abstract class IProgramMethod {
}

abstract class IProgramVariable {
}

class LocationVariable extends ProgramVariable {
}

class ProgramConstant extends ProgramVariable {
}

class ProgramMethod extends ObserverFunction {
}

class ProgramSV extends JOperatorSV {
}

abstract class ProgramVariable extends JAbstractSortedOperator {
}

abstract class AbstractProgramElement {
}

class ArrayLength extends ProgramTransformer {
}

class ArrayPostDecl extends ProgramTransformer {
}

class ConstructorCall extends ProgramTransformer {
}

class CreateObject extends ProgramTransformer {
}

class DoBreak extends ProgramTransformer {
}

class EnhancedForElimination extends ProgramTransformer {
}

class EvaluateArgs extends ProgramTransformer {
}

class ExpandMethodBody extends ProgramTransformer {
}

class ForInitUnfoldTransformer extends ProgramTransformer {
}

class ForToWhile extends ProgramTransformer {
}

abstract class InitArray extends ProgramTransformer {
}

class InitArrayCreation extends InitArray {
}

class IsStatic extends ProgramTransformer {}

class MethodCall extends ProgramTransformer {
    MethodReference methRef;
    ReferencePrefix newContext;
    ProgramVariable pvar;
    List<Expression> arguments;
    KeYJavaType staticPrefixType;
}

class MultipleVarDecl extends ProgramTransformer {
}

class PostWork extends ProgramTransformer {
}

abstract class ProgramTransformer extends JavaNonTerminalProgramElement {
}

class ReattachLoopInvariant extends ProgramTransformer {
}

class SpecialConstructorCall extends ProgramTransformer {
}

class StaticInitialisation extends ProgramTransformer {
}

class SwitchToIf extends ProgramTransformer {
}

class TypeOf extends ProgramTransformer {
}

class Unpack extends ProgramTransformer {
}

class UnwindLoop extends ProgramTransformer {
}
