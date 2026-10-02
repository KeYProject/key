package org.key_project.java.ast;

import org.jspecify.annotations.Nullable;
import de.uka.ilkd.key.speclang.jml.pretranslation.*;
import de.uka.ilkd.key.java.ast.PositionInfo;
import org.key_project.util.collection.*;
import de.uka.ilkd.key.rule.MatchConditions;
import de.uka.ilkd.key.java.ast.abstraction.KeYJavaType;
import org.key_project.logic.op.sv.*;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.abstraction.Type;
import org.jspecify.annotations.NullMarked;

@Root
@NullMarked()
public sealed abstract class JavaSourceElement implements Visitable, Matchable permits AnnotationUseSpecification, ArrayDeclaration, ArrayInitializer, ArrayLength, ArrayLengthReference, ArrayPostDecl, ArrayReference, Assert, Assignment, BinaryOperator, BooleanLiteral, Break, Case, Catch, CatchAllStatement, Ccatch, CcatchNonstandardParameterDeclaration, ClassInitializer, Comment, CompilationUnit, Conditional, ConstructorCall, ConstructorDeclaration, ContextStatementBlock, Continue, CreateObject, DLEmbeddedExpression, Default, Do, DoBreak, DoubleLiteral, EmptyStatement, EnhancedFor, EnhancedForElimination, EnumClassDeclaration, EvaluateArgs, ExactInstanceof, Exec, ExecutionContext, ExpandMethodBody, Extends, FieldDeclaration, FieldSpecification, FloatLiteral, For, ForInitUnfoldTransformer, ForToWhile, ForUpdates, FreeLiteral, Guard, If, Implements, Import, InitArrayCreation, Instanceof, IntLiteral, InterfaceDeclaration, IsStatic, JMLModifiers, JmlAssert, LabeledStatement, LocalVariableDeclaration, LocationVariable, LogicalFunctionOperator, LongLiteral, LoopInit, LoopScopeBlock, MergePointStatement, MetaClassReference, MethodBodyStatement, MethodCall, MethodFrame, MethodReference, MultipleVarDecl, New, NewArray, PackageReference, ParameterDeclaration, ParenthesizedExpression, PassiveExpression, PermIndProgramElementName, PostWork, ProgramConstant, ProgramMethod, ProgramSV, RealLiteral, ReattachLoopInvariant, Return, SchemaTypeReference, SchematicFieldReference, SetStatement, SingleCatch, SpecialConstructorCall, StaticInitialisation, StringLiteral, SuperArrayDeclaration, SuperConstructorReference, SuperReference, Switch, SwitchToIf, SynchronizedBlock, TempIndProgramElementName, ThisConstructorReference, ThisReference, Throw, Throws, TransactionStatement, Try, TypeCast, TypeOf, TypeRef, UnaryOperator, Unpack, UnwindLoop, While {

    @Nullable()
    public abstract PositionInfo positionInfo();
}
