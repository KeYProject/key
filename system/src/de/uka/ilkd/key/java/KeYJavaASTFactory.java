// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.java;

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.abstraction.Type;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.ArrayInitializer;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.PassiveExpression;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.literal.NullLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.Equals;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.expression.operator.LogicalAnd;
import de.uka.ilkd.key.java.expression.operator.LogicalOr;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.expression.operator.NewArray;
import de.uka.ilkd.key.java.expression.operator.NotEquals;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.IExecutionContext;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SuperConstructorReference;
import de.uka.ilkd.key.java.reference.SuperReference;
import de.uka.ilkd.key.java.reference.ThisConstructorReference;
import de.uka.ilkd.key.java.reference.ThisReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.Branch;
import de.uka.ilkd.key.java.statement.Break;
import de.uka.ilkd.key.java.statement.Case;
import de.uka.ilkd.key.java.statement.Catch;
import de.uka.ilkd.key.java.statement.Continue;
import de.uka.ilkd.key.java.statement.Default;
import de.uka.ilkd.key.java.statement.Do;
import de.uka.ilkd.key.java.statement.Else;
import de.uka.ilkd.key.java.statement.EmptyStatement;
import de.uka.ilkd.key.java.statement.EnhancedFor;
import de.uka.ilkd.key.java.statement.Finally;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.ForUpdates;
import de.uka.ilkd.key.java.statement.Guard;
import de.uka.ilkd.key.java.statement.IForUpdates;
import de.uka.ilkd.key.java.statement.IGuard;
import de.uka.ilkd.key.java.statement.ILoopInit;
import de.uka.ilkd.key.java.statement.If;
import de.uka.ilkd.key.java.statement.LabeledStatement;
import de.uka.ilkd.key.java.statement.LoopInit;
import de.uka.ilkd.key.java.statement.MethodBodyStatement;
import de.uka.ilkd.key.java.statement.MethodFrame;
import de.uka.ilkd.key.java.statement.Return;
import de.uka.ilkd.key.java.statement.Switch;
import de.uka.ilkd.key.java.statement.SynchronizedBlock;
import de.uka.ilkd.key.java.statement.Then;
import de.uka.ilkd.key.java.statement.Throw;
import de.uka.ilkd.key.java.statement.TransactionStatement;
import de.uka.ilkd.key.java.statement.Try;
import de.uka.ilkd.key.java.statement.While;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.util.ExtList;

/**
 * The KeYASTFactory helps building KeY Java AST structures.
 */
public abstract class KeYJavaASTFactory {

    /**
     * creates an assignment <code> lhs:=rhs </code>
     */
    public static CopyAssignment assign(Expression lhs, Expression rhs) {
	return new CopyAssignment(lhs, rhs);
    }

    /**
     * creates an assignment <code> lhs:=rhs </code>
     */
    public static CopyAssignment assign(Expression lhs, Expression rhs,
	    PositionInfo posInfo) {
	return assign(new ExtList(new Object[] { lhs, rhs, posInfo }));
    }

    /**
     * Create an assignment.
     * 
     * @param parameters
     *            the assignment parameters (variable, expression) as
     *            {@link ExtList}
     * @return a new {@link CopyAssignment} as defined by
     *         <code>parameters</code>
     */
    public static CopyAssignment assign(final ExtList parameters) {
	final CopyAssignment assignment = new CopyAssignment(parameters);

	return assignment;
    }

    /**
     * creates an attribute access <code>prefix.field </code>
     */
    public static Expression attribute(ReferencePrefix prefix,
	    ProgramVariable field) {
	return new FieldReference(field, prefix);
    }

    /**
     * creates a local variable declaration <code> typeRef name; </code>
     */
    public static LocalVariableDeclaration declare
	(ProgramElementName name, TypeReference typeRef) {
	return new LocalVariableDeclaration
	    (typeRef, new VariableSpecification
	     (new LocationVariable(name,
				  typeRef.getKeYJavaType())));
    }

    /**
     * Create a local variable declaration without initialization.
     * 
     * <pre>
     * type name;
     * </pre>
     * 
     * @param name
     *            the {@link ProgramElementName} of the variable to be declared
     * @param type
     *            the static {@link KeYJavaType} of the variable to be declared
     * @return a new {@link LocalVariableDeclaration} of a variable with static
     *         type <code>type</code> and name <code>name</code>
     */
    public static LocalVariableDeclaration declare(
	    final ProgramElementName name, final KeYJavaType type) {
	final LocalVariableDeclaration declaration = KeYJavaASTFactory.declare(
		name, null, type);

	return declaration;
    }

    /**
     * create a local variable declaration <br></br>
     *   <code>type name = init; </code>
     */
    public static LocalVariableDeclaration declare
	(ProgramElementName name, Expression init, KeYJavaType type) {
	return new LocalVariableDeclaration
	    (new TypeRef(type),
	     new VariableSpecification
		 (new LocationVariable(name, type),
		  init, type));
    }

    /**
     * Create a local variable declaration.
     * 
     * <pre>
     * type var = init;
     * </pre>
     * 
     * @param var
     *            the named and typed {@link IProgramVariable} to be declared
     * @param init
     *            the {@link Expression} <code>var</code> is initialized with
     * @param type
     *            the static {@link KeYJavaType} of <code>var</code>
     * @return a {@link LocalVariableDeclaration} of <code>var</code> with
     *         static type <code>type</code> and initial value <code>init</code>
     */
    public static LocalVariableDeclaration declare
	(IProgramVariable var, Expression init, KeYJavaType type) {
	return KeYJavaASTFactory.declare(new Modifier[0], var, init, type);
    }

    /**
     * Create a local variable declaration with a unique name.
     * 
     * <pre>
     * type name{unique} = initializer;
     * </pre>
     * 
     * @param services
     *            the {@link Services} whose {@link VariableNamer} is used to
     *            determine a unique variable name
     * @param name
     *            the {@link String} on which the variable's unique name is
     *            based
     * @param initializer
     *            the {@link Expression} the declared variable is initialized
     *            with
     * @param type
     *            the static {@link KeYJavaType} of the to be declared variable
     * @return a {@link LocalVariableDeclaration} of variable named uniquely
     *         after <code>name</code> with static type <code>type</code> and
     *         initial value <code>initializer</code>
     */
    public static LocalVariableDeclaration declare(final Services services,
	    final String name, final Expression initializer,
	    final KeYJavaType type) {
	final ProgramElementName uniqueName = services.getVariableNamer()
		.getTemporaryNameProposal(name);
	final LocalVariableDeclaration declaration = KeYJavaASTFactory.declare(
		uniqueName, initializer, type);

	return declaration;
    }

    /**
     * Create a local variable declaration without initialization.
     * 
     * <pre>
     * type var;
     * </pre>
     * 
     * @param var
     *            the named and typed {@link IProgramVariable} to be declared
     * @param type
     *            the static {@link KeYJavaType} of <code>var</code>
     * @return a {@link LocalVariableDeclaration} of <code>var</code> with
     *         static type <code>type</code>
     */
    public static LocalVariableDeclaration declare
	(IProgramVariable var, KeYJavaType type) {
	return KeYJavaASTFactory.declare(var, null, type);
    }

    /**
     * create a local variable declaration
     */
    public static LocalVariableDeclaration declare(String name, KeYJavaType type) {
	return new LocalVariableDeclaration
	    (new TypeRef(type),
	     new VariableSpecification
		 (new LocationVariable(new ProgramElementName(name), type)));
    }

    /**
     * create a parameter declaration
     */

    public static ParameterDeclaration parameterDeclaration(JavaInfo javaInfo,
							    KeYJavaType kjt,
							    String name) {
	return new ParameterDeclaration
	    (new Modifier[0], javaInfo.createTypeReference(kjt),
	     new VariableSpecification(localVariable(name, kjt)), false);
    }

    /**
     * Create a parameter declaration.
     * 
     * <pre>
     * kjt var
     * </pre>
     * 
     * @param javaInfo
     *            the Java model containing <code>kjt</code>
     * @param kjt
     *            the static {@link KeYJavaType} of <code>var</code>
     * @param var
     *            the named and typed {@link IProgramVariable} to be declared as
     *            parameter
     * @return a {@link ParameterDeclaration} of <code>var</code> with static
     *         type <code>kjt</code>
     */
    public static ParameterDeclaration parameterDeclaration(JavaInfo javaInfo,
							    KeYJavaType kjt,
							    IProgramVariable var) {
	return new ParameterDeclaration
	    (new Modifier[0], javaInfo.createTypeReference(kjt),
	     new VariableSpecification(var), false);
    }

    public static ParameterDeclaration parameterDeclaration(JavaInfo javaInfo,
							    String type,
							    String name) {
	KeYJavaType kjt = javaInfo.getKeYJavaType(type);
	return new ParameterDeclaration
	    (new Modifier[0], javaInfo.createTypeReference(kjt),
	     new VariableSpecification(localVariable(name, kjt)), false);
    }

    /**
     * Create a parenthesized expression.
     * 
     * <pre>
     * (expression)
     * </pre>
     * 
     * @param expression
     *            the {@link Expression} to be parenthesized
     * @return a new {@link ParenthesizedExpression} of <code>expression</code>
     */
    public static ParenthesizedExpression parenthesizedExpression(
	    final Expression expression) {
	final ParenthesizedExpression parenthesized = new ParenthesizedExpression(
		expression);

	return parenthesized;
    }

    /**
     * Create an inactive expression.
     * 
     * @param expression
     *            the {@link Expression} to be marked inactive
     * @return a new {@link PassiveExpression} version of
     *         <code>expression</code>
     */
    public static PassiveExpression passiveExpression(
	    final Expression expression) {
	final PassiveExpression passive = new PassiveExpression(expression);

	return passive;
    }

    /**
     * create a local variable
     */
    public static ProgramVariable localVariable(String name,
						KeYJavaType kjt) {
	return localVariable(new ProgramElementName(name), kjt);
    }

    /**
     * create a local variable
     */
    public static ProgramVariable localVariable(ProgramElementName name,
	    KeYJavaType kjt) {
	return new LocationVariable(name, kjt);
    }

    /**
     * Create a local variable with a unique name.
     * 
     * @param services
     *            the {@link Services} whose {@link VariableNamer} is used
     * @param name
     *            the {@link String} on which the variable's unique name is
     *            based
     * @param type
     *            the variable's static {@link KeYJavaType}
     * @return a new {@link ProgramVariable} of static type <code>type</code>
     *         and with a unique name based on <code>name</code>
     */
    public static ProgramVariable localVariable(final Services services,
	    final String name, final KeYJavaType type) {
	final ProgramElementName uniqueName = services.getVariableNamer()
		.getTemporaryNameProposal(name);
	final ProgramVariable variable = KeYJavaASTFactory.localVariable(
		uniqueName, type);

	return variable;
    }

    /**
     * Create a logical and operator.
     * 
     * <pre>
     * left &amp; right
     * </pre>
     * 
     * @param left
     *            the left operand {@link Expression}
     * @param right
     *            the right operand <code>Expression</code>
     * @return a new {@link LogicalAnd} of <code>left</code> and
     *         <code>right</code>
     */
    public static LogicalAnd logicalAndOperator(final Expression left,
	    final Expression right) {
	final LogicalAnd operator = new LogicalAnd(left, right);

	return operator;
    }

    /**
     * Create a logical or operator.
     * 
     * <pre>
     * left | right
     * </pre>
     * 
     * @param left
     *            the left operand {@link Expression}
     * @param right
     *            the right operand {@link Expression}
     * @return a new {@link LogicalOr} of <code>left</code> and
     *         <code>right</code>
     */
    public static LogicalOr logicalOrOperator(final Expression left,
	    final Expression right) {
	final LogicalOr operator = new LogicalOr(left, right);

	return operator;
    }

    /**
     * Create a catch clause.
     * 
     * @param parameters
     *            the catch clause parameters (exception, body) as
     *            {@link ExtList}
     * @return a new {@link Catch} as defined by <code>parameters</code>
     */
    public static Catch catchClause(final ExtList parameters) {
	final Catch clause = new Catch(parameters);

	return clause;
    }

    /**
     * create a catch clause
     */

    public static Catch catchClause(ParameterDeclaration param,
	    StatementBlock body) {

	return new Catch(param, body);
    }

    /**
     * Create a catch clause.
     * 
     * <pre>
     * catch (parameter) {
     *     statements
     * }
     * </pre>
     * 
     * @param parameter
     *            the to be caught {@link ParameterDeclaration}
     * @param statements
     *            the body {@link Statement}s
     * @return a new {@link Catch} clause for execution of
     *         <code>statements</code> in case of <code>parameter</code>
     */
    public static Catch catchClause(final ParameterDeclaration parameter,
	    final Statement[] statements) {
	final StatementBlock body = KeYJavaASTFactory.block(statements);
	final Catch clause = KeYJavaASTFactory.catchClause(parameter, body);

	return clause;
    }

    /**
     * Create a catch clause.
     * 
     * <pre>
     * catch (kjt param)
     *    body
     * </pre>
     * 
     * @param javaInfo
     *            the {@link JavaInfo} containing <code>kjt</code>
     * @param param
     *            the {@link String} name of the exception object variable
     * @param kjt
     *            the {@link KeYJavaType} of the exception object variable
     * @param body
     *            the {@link StatementBlock} catch clause body
     * @return a new {@link Catch} with parameter <code>param</code> of static
     *         type <code>kjt</code> and body <code>body</code>
     */
    public static Catch catchClause(JavaInfo javaInfo, String param,
	    KeYJavaType kjt, StatementBlock body) {

	return new Catch(parameterDeclaration(javaInfo, kjt, param), body);
    }

    /**
     * Create a catch clause.
     * 
     * <pre>
     * catch (type param)
     *    body
     * </pre>
     * 
     * @param javaInfo
     *            the {@link JavaInfo} containing a {@link KeYJavaType} named
     *            <code>type</code>
     * @param param
     *            the {@link String} name of the exception object variable
     * @param type
     *            the <code>String</code> name of the exception object
     *            variable's <code>KeYJavaType</code>
     * @param body
     *            the {@link StatementBlock} catch clause body
     * @return a new {@link Catch} with parameter <code>param</code> of static
     *         type <code>type</code> and body <code>body</code>
     */
    public static Catch catchClause(JavaInfo javaInfo, String param,
	    String type, StatementBlock body) {

	return catchClause(javaInfo, param,
			   javaInfo.getKeYJavaType(type), body);
    }

    /**
     * Create a throw clause.
     * 
     * <pre>
     * throw e
     * </pre>
     * 
     * @param e
     *            the throw {@link Expression}
     * @return a new {@link Throw} statement with expression <code>e</code>
     */
    public static Throw throwClause(Expression e) {
	return new Throw(e);
    }

    /**
     * Create a transaction statement.
     * 
     * @param type
     *            the transaction statement type
     * @return a new {@link TransactionStatement} of type <code>type</code>
     */
    public static TransactionStatement transactionStatement(final int type) {
	final TransactionStatement statement = new TransactionStatement(type);

	return statement;
    }

    /**
     * Create a <code>true</code> condition.
     * 
     * @return a new {@link Guard} with expression <code>true</code>
     */
    public static Guard trueGuard() {
	final Guard guard = new Guard(BooleanLiteral.TRUE);

	return guard;
    }

    /**
     * Create a while loop.
     * 
     * <pre>
     * while (condition)
     *     body
     * </pre>
     * 
     * @param condition
     *            the loop condition {@link Expression}
     * @param body
     *            the loop body {@link Statement}
     * @return a new {@link While} loop defined by <code>condition</code> and
     *         <code>body</code>
     */
    public static Statement whileLoop(final Expression condition,
	    final Statement body) {
	final While loop = new While(condition, body);

	return loop;
    }

    /**
     * Create a while loop at a specific source position.
     * 
     * <pre>
     * while (condition)
     *     body
     * </pre>
     * 
     * @param condition
     *            the loop condition {@link Expression}
     * @param body
     *            the loop body {@link Statement}
     * @param position
     *            the new source element's {@link PositionInfo}
     * @return a new {@link While} loop defined by <code>condition</code> and
     *         <code>body</code>, and positioned at <code>position</code>
     */
    public static While whileLoop(final Expression condition,
	    final Statement body, final PositionInfo position) {
	final While loop = new While(condition, body, position);

	return loop;
    }

    /**
     * Create a return clause.
     * 
     * <pre>
     * return e
     * </pre>
     * 
     * @param e
     *            the return {@link Expression}
     * @return a new {@link Return} statement with expression <code>e</code>
     */
    public static Return returnClause(Expression e) {
	return new Return(e);
    }

    /**
     * Create an if statement with no else branch.
     * 
     * <pre>
     * if (guard)
     *    then
     * </pre>
     * 
     * @param guard
     *            the if statement condition {@link Expression}
     * @param then
     *            the if statement then branch {@link Statement}
     * @return an {@link If} with expression <code>guard</code> and then branch
     *         <code>then</code>
     */
    public static If ifThen(Expression guard,
			    Statement then) {
	final If statement = KeYJavaASTFactory.ifThen(guard, new Then(then));

	return statement;
    }

    /**
     * Create an if statement with no else branch.
     * 
     * <pre>
     * if (guard) {
     *    statements
     * }
     * </pre>
     * 
     * @param guard
     *            the if statement condition {@link Expression}
     * @param statements
     *            the if statement then branch {@link Statement}s
     * @return an {@link If} with condition <code>guard</code> and then branch
     *         <code>statements</code>
     */
    public static If ifThen(final Expression guard,
	    final Statement... statements) {
	final StatementBlock block = KeYJavaASTFactory.block(statements);
	final If statement = KeYJavaASTFactory.ifThen(guard, block);

	return statement;
    }

    /**
     * Create an if statement with no else branch.
     * 
     * <pre>
     * if (guard)
     *    then
     * </pre>
     * 
     * @param guard
     *            the if statement condition {@link Expression}
     * @param then
     *            the if statement then branch {@link Then}
     * @return an {@link If} with expression <code>guard</code> and then branch
     *         <code>then</code>
     */
    public static If ifThen(final Expression guard, final Then then) {
	final If statement = new If(guard, then);

	return statement;
    }

    /**
     * Create an if statement.
     * 
     * @param parameters
     *            the if statement parameters (guard, body, else branch) as
     *            {@link ExtList}
     * @return a new {@link If} as defined by <code>parameters</code>
     */
    public static If ifStatement(final ExtList parameters) {
	final If statement = new If(parameters);

	return statement;
    }

    /**
     * Create an if statement including an else branch.
     * 
     * <pre>
     * if (guard)
     *    then
     * else
     *    els
     * </pre>
     * 
     * @param guard
     *            the if statement condition {@link Expression}
     * @param then
     *            the if statement then branch {@link Statement}
     * @param els
     *            the if statement else branch <code>Statement</code>
     * @return an {@link If} with expression <code>guard</code>, then branch
     *         <code>then</code> and else branch <code>els</code>
     */
    public static If ifElse(Expression guard,
		     Then then,
		     Else els) {
	return new If(guard, then, els);
    }

    /**
     * Create an if clause.
     * 
     * <pre>
     * if (guard)
     *    thenStatement
     * else
     *    elseStatement
     * </pre>
     * 
     * @param guard
     *            the if clause condition {@link Expression}
     * 
     * @param thenStatement
     *            the if clause then branch {@link Statement}
     * 
     * @param elseStatement
     *            the if clause else branch <code>Statement</code>
     * 
     * @return a new {@link If} with condition <code>guard</code>, then branch
     *         <code>thenStatement</code> and else branch
     *         <code>elseStatement</code>
     */
    public static Statement ifElse(final Expression guard,
	    final Statement thenStatement, final Statement elseStatement) {
	final Then then = new Then(thenStatement);
	final Else els = new Else(elseStatement);
	final If ifElse = KeYJavaASTFactory.ifElse(guard, then, els);

	return ifElse;
    }

    /**
     * Create a break statement.
     * 
     * @param l
     *            the break destination {@link Label}
     * @return a new {@link Break} with label <code>l</code>
     */
    public static Break breakStatement(Label l) {
	return new Break(l);
    }

    public static Statement breakStatement(Label label, PositionInfo positionInfo) {
       return new Break(new ExtList(new Object[] {label, positionInfo}));
    }

    /**
     * Create a case block.
     * 
     * @param parameters
     *            the case block parameters (body) as {@link ExtList}
     * @param expression
     *            the case block {@link Expression}
     * @param position
     *            the new source element's {@link PositionInfo}
     * @return a new {@link Case} as defined by <code>parameters</code> and
     *         <code>expression</code>
     */
    public static Case caseBlock(final ExtList parameters,
	    final Expression expression, final PositionInfo position) {
	final Case block = new Case(parameters, expression, position);

	return block;
    }

    /**
     * Create a case block.
     * 
     * <pre>
     * case (expression)
     *     statement
     * </pre>
     * 
     * @param expression
     *            the case {@link Expression}
     * @param statement
     *            the to be executed {@link Statement}
     * @return a new {@link Case} for execution of <code>statement</code> in
     *         case of <code>expression</code>
     */
    public static Case caseBlock(final Expression expression,
	    final Statement statement) {
	final Statement[] statements = new Statement[] { statement };
	final Case block = KeYJavaASTFactory.caseBlock(expression, statements);

	return block;
    }

    /**
     * Create a case block.
     * 
     * <pre>
     * case (expression) {
     *     statements
     * }
     * </pre>
     * 
     * @param expression
     *            the case {@link Expression}
     * @param statements
     *            the to be executed {@link Statement}s
     * @return a new {@link Case} for execution of <code>statements</code> in
     *         case of <code>expression</code>
     */
    public static Case caseBlock(final Expression expression,
	    final Statement[] statements) {
	final Case block = new Case(expression, statements);

	return block;
    }

    public static Continue continueStatement(Label label) {
	return new Continue(label);
    }

    /**
     * Create an empty statement.
     * 
     * @return a new {@link EmptyStatement}
     */
    public static EmptyStatement emptyStatement() {
	return new EmptyStatement();
    }

    /**
     * Create an enhanced for loop.
     * 
     * @param parameters
     *            the loop definition parameters (initializer, guard, body) as
     *            {@link ExtList}
     * @return a new {@link For} as defined by <code>parameters</code>
     */
    public static EnhancedFor enhancedForLoop(final ExtList parameters) {
	final EnhancedFor loop = new EnhancedFor(parameters);

	return loop;
    }

    /**
     * Create an equality comparison with <code>null</code>.
     * 
     * <pre>
     * expression == null
     * </pre>
     * 
     * @param expression
     *            the {@link Expression} to be compared against
     *            <code>null</code>
     * @return a new {@link Equals} that compares <code>expression</code>
     *         against <code>null</code>
     */
    public static Equals equalsNullOperator(final Expression expression) {
	final Equals operator = KeYJavaASTFactory.equalsOperator(expression,
		NullLiteral.NULL);

	return operator;
    }

    /**
     * Create an equals operator.
     * 
     * <pre>
     * left == right
     * </pre>
     * 
     * @param left
     *            the left operand {@link Expression}
     * @param right
     *            the right operand <code>Expression</code>
     * @return a new {@link Equals} of <code>left</code> and <code>right</code>
     */
    public static Equals equalsOperator(final Expression left,
	    final Expression right) {
	final Equals statement = new Equals(left, right);

	return statement;
    }

    /**
     * Create an equals operator.
     * 
     * <pre>
     * operand{1} == operand{2}
     * </pre>
     * 
     * @param operands
     *            the operands {@link ExtList}
     * @return a new {@link Equals} of <code>operands</code>
     */
    public static Equals equalsOperator(final ExtList operands) {
	final Equals statement = new Equals(operands);

	return statement;
    }

    /**
     * Create an execution context.
     * 
     * @param classType
     *            the enclosing class {@link KeYJavaType}
     * @param method
     *            the enclosing {@link IProgramMethod} defined in
     *            <code>classType</code>
     * @param reference
     *            the {@link ReferencePrefix} <code>method</code> is called on
     * @return a new {@link ExecutionContext} for calls on
     *         <code>reference</code> to <code>method</code> from
     *         <code>classType</code>
     */
    public static ExecutionContext executionContext(
	    final KeYJavaType classType, final IProgramMethod method,
	    final ReferencePrefix reference) {
	final TypeRef type = new TypeRef(classType);
	final ExecutionContext context = new ExecutionContext(type, method,
		reference);

	return context;
    }

    /**
     * Insert a statement in a block of statements.
     * 
     * @param statement
     *            the {@link Statement} to be inserted into <code>block</code>
     * @param block
     *            the {@link StatementBlock} <code>statement</code> is inserted
     *            into
     * @return a new <code>StatementBlock</code> that contains both the
     *         <code>Statement</code>s from <code>block</code> and
     *         <code>statement</code>
     */
    public static StatementBlock insertStatementInBlock(
	    final Statement statement, final StatementBlock block) {
	final Statement[] statements = new Statement[] { statement };
	final StatementBlock statementBlock = KeYJavaASTFactory
		.insertStatementInBlock(statements, block);

	return statementBlock;
    }

    /** inserts the given statements at the begin of the block
     * @param stmnt array of Statement those have to be inserted
     * @param b the Statementblock where to insert
     */
    public static StatementBlock insertStatementInBlock(Statement[] stmnt,
	    StatementBlock b) {

	Statement[] block = new Statement[b.getStatementCount()+
					  stmnt.length];
	System.arraycopy(stmnt, 0, block, 0, stmnt.length);
	b.getBody().arraycopy(0, block, stmnt.length, b.getStatementCount());
	return new StatementBlock(new ImmutableArray<Statement>(block));
    }

    /** inserts the given statements at the begin of the block
     * @param stmnt array of Statement those have to be inserted
     * @param b the Statementblock where to insert
     */
    public static StatementBlock insertStatementInBlock(StatementBlock stmnt,
	    StatementBlock b) {
	Statement[] stmnts = new Statement[stmnt.getStatementCount()];
	for (int i=0; i<stmnt.getStatementCount(); i++)
	    stmnts[i]=stmnt.getStatementAt(i);
	return
	    insertStatementInBlock(stmnts, b);
    }

    /**
     * Create a block where the given statements come after the given block.
     * 
     * <pre>
     * block
     * statements
     * </pre>
     * 
     * @param block
     *            the original {@link StatementBlock}
     * @param statements
     *            the inserted {@link Statement}s
     * @return a new <code>StatementBlock</code> that contains
     *         <code>block</code> first and <code>statements</code> second
     */
    public static StatementBlock insertStatementInBlock(
	    final StatementBlock block, Statement[] statements) {
	final StatementBlock blockEnd = KeYJavaASTFactory.block(statements);
	final StatementBlock blockComplete = KeYJavaASTFactory
		.insertStatementInBlock(block, blockEnd);

	return blockComplete;
    }

    /**
     * Create an instance of operator.
     * 
     * <pre>
     * expression instance of type
     * </pre>
     * 
     * @param expression
     *            the {@link Expression} operand, whose runtime type is to be
     *            checked
     * @param type
     *            the {@link KeYJavaType} operand <code>expression</code>'s type
     *            is checked against
     * @return a new {@link Instanceof} for checking <code>expression</code>'s
     *         type against <code>type</code>
     */
    public static Instanceof instanceOf(final Expression expression,
	    final KeYJavaType type) {
	final TypeRef typeRef = new TypeRef(type);
	final Instanceof instanceOf = new Instanceof(expression, typeRef);

	return instanceOf;
    }

    /**
     * Create a local variable declaration that assigns zero initially.
     * 
     * <pre>
     * type variable = 0;
     * </pre>
     * 
     * @param type
     *            the static {@link KeYJavaType} of <code>variable</code>
     * @param variable
     *            the named and typed {@link IProgramVariable} to be declared
     * @return a new {@link LocalVariableDeclaration} of <code>variable</code>
     *         with static type <code>type</code> and initial value zero
     */
    public static LocalVariableDeclaration declareZero(final KeYJavaType type,
	    final IProgramVariable variable) {
	final IntLiteral zeroLiteral = KeYJavaASTFactory.zeroLiteral();

	return KeYJavaASTFactory.declare(variable, zeroLiteral, type);
    }

    /**
     * Create a local variable declaration that assigns a method's return value
     * initially.
     * 
     * <pre>
     * type variable = reference.method();
     * </pre>
     * 
     * @param type
     *            the static {@link KeYJavaType} of <code>variable</code>
     * @param variable
     *            the named and typed {@link IProgramVariable} to be declared
     * @param reference
     *            the {@link ReferencePrefix} the method is called on
     * @param method
     *            the method's name {@link String}
     * @return a new {@link LocalVariableDeclaration} of <code>variable</code>
     *         with static type <code>type</code> and initial value
     *         <code>reference.method()</code>
     */
    public static LocalVariableDeclaration declareMethodCall(
	    final KeYJavaType type, final IProgramVariable variable,
	    final ReferencePrefix reference, final String method) {
	final MethodReference call = KeYJavaASTFactory.methodCall(reference,
		method);

	return KeYJavaASTFactory.declare(variable, call, type);
    }

    /**
     * Create a local variable declaration that assigns a method's return value
     * initially.
     * 
     * <pre>
     * type variable = reference.method();
     * </pre>
     * 
     * where <code>type</code> is variable's {@link KeYJavaType} as it is
     * returned by {@link IProgramVariable#getKeYJavaType()}.
     * 
     * @param variable
     *            the named and typed {@link IProgramVariable} to be declared
     * @param reference
     *            the {@link ReferencePrefix} the method is called on
     * @param method
     *            the method's name {@link String}
     * @return a new {@link LocalVariableDeclaration} of <code>variable</code>
     *         with static type <code>type</code> and initial value
     *         <code>reference.method()</code>
     */
    public static LocalVariableDeclaration declareMethodCall(
	    final IProgramVariable variable, final ReferencePrefix reference,
	    final String method) {
	final MethodReference call = KeYJavaASTFactory.methodCall(reference,
		method);

	return KeYJavaASTFactory.declare(variable, call);
    }

    /**
     * Create a default block.
     * 
     * @param parameters
     *            the default block parameters (body) as {@link ExtList}
     * @return a new {@link Default} as defined by <code>parameters</code>
     */
    public static Default defaultBlock(final ExtList parameters) {
	final Default block = new Default(parameters);

	return block;
    }

    /**
     * Create a default block.
     * 
     * <pre>
     * default
     *     statement
     * </pre>
     * 
     * @param statement
     *            the to be executed {@link Statement}
     * @return a new {@link Default} that contains <code>statement</code>
     */
    public static Default defaultBlock(final Statement statement) {
	final Statement[] statements = new Statement[] { statement };
	final Default block = KeYJavaASTFactory.defaultBlock(statements);

	return block;
    }

    /**
     * Create a default block.
     * 
     * <pre>
     * default {
     *     statements
     * }
     * </pre>
     * 
     * @param statements
     *            the to be executed {@link Statement}s
     * @return a new {@link Default} that contains <code>statements</code>
     */
    public static Default defaultBlock(final Statement[] statements) {
	final Default block = new Default(statements);

	return block;
    }

    /**
     * Create a do loop.
     * 
     * <pre>
     * do
     *     statement
     * while (condition);
     * </pre>
     * 
     * @param condition
     *            the do-loop condition {@link Expression}
     * @param statement
     *            the do-loop body {@link Statement}
     * @param positionInfo
     *            the new source element's {@link PositionInfo}
     * @return a new {@link Do} that executes <code>statement</code> while
     *         <code>condition</code> holds
     */
    public static Do doLoop(final Expression condition,
	    final Statement statement, final PositionInfo positionInfo) {
	final Do loop = new Do(condition, statement, positionInfo);

	return loop;
    }

    /**
     * Create an else block.
     * 
     * @param parameters
     *            the else block parameters (body) as {@link ExtList}
     * @return a new {@link Else} as defined by <code>parameters</code>
     */
    public static Else elseBlock(final ExtList parameters) {
	final Else block = new Else(parameters);

	return block;
    }

    /**
     * Create an else block.
     * 
     * <pre>
     * else
     *     statement
     * </pre>
     * 
     * @param statement
     *            the {@link Statement} to be executed
     * @return a new {@link Else} block consisting of <code>statement</code>
     *         solely
     */
    public static Else elseBlock(final Statement statement) {
	final Else block = new Else(statement);

	return block;
    }

    /**
     * Create an else block.
     * 
     * <pre>
     * else {
     *     statements
     * }
     * </pre>
     * 
     * @param statements
     *            the {@link Statement}s to be executed
     * @return a new {@link Else} block consisting of <code>statements</code>
     *         solely
     */
    public static Else elseBlock(final Statement[] statements) {
	final StatementBlock statement = KeYJavaASTFactory.block(statements);
	final Else block = KeYJavaASTFactory.elseBlock(statement);

	return block;
    }

    /**
     * Create a loop initialization that consists of a single statement.
     * 
     * <pre>
     * init
     * </pre>
     * 
     * @param init
     *            the single {@link LoopInitializer}
     * @return a new {@link ILoopInit} that consists of <code>init</code> only
     */
    public static ILoopInit loopInit(final LoopInitializer init) {
	final LoopInitializer[] initializers = { init };

	return new LoopInit(initializers);
    }

    /**
     * Create a loop initialization that declares and assigns zero to a local
     * variable.
     * 
     * <pre>
     * type variable = 0
     * </pre>
     * 
     * @param type
     *            the static {@link KeYJavaType} of <code>variable</code>
     * @param variable
     *            the named and typed {@link IProgramVariable} to be declared
     * @return a new {@link ILoopInit} that declares variable
     *         <code>variable</code> with static type <code>type</code> and
     *         initial value zero
     */
    public static ILoopInit loopInitZero(final KeYJavaType type,
	    final IProgramVariable variable) {
	final LoopInitializer initializer = KeYJavaASTFactory.declareZero(type,
		variable);

	return KeYJavaASTFactory.loopInit(initializer);
    }

    /**
     * Create an array initializer.
     * 
     * @param expressions
     *            the initial value {@link Expression}s
     * @param type
     *            the array type {@link KeYJavaType}
     * @return a new {@link ArrayInitializer} which contains
     *         <code>expressions</code> and is of type <code>type</code>
     */
    public static ArrayInitializer arrayInitializer(
	    final Expression[] expressions, final KeYJavaType type) {
	final ArrayInitializer initializer = new ArrayInitializer(expressions,
		type);

	return initializer;
    }

    /**
     * Create an array length access.
     * 
     * <pre>
     * array.length
     * </pre>
     * 
     * @param model
     *            the {@link JavaInfo} to retrieve the array super class type,
     *            which holds the length attribute, from
     * @param array
     *            the {@link ReferencePrefix} whose length attribute is accessed
     * @return a new {@link FieldReference} for <code>array</code>'s length
     *         attribute
     */
    public static FieldReference arrayLength(final JavaInfo model,
	    final ReferencePrefix array) {
	final ProgramVariable lengthField = model.getArrayLength();
	final FieldReference reference = new FieldReference(lengthField, array);

	return reference;
    }

    /**
     * Create a condition that compares two expressions using the less than
     * operator.
     * 
     * <pre>
     * left &lt; right
     * </pre>
     * 
     * @param left
     *            the {@link Expression} to be compared less than
     *            <code>right</code>
     * @param right
     *            the <code>Expression</code> to be compared greater than
     *            <code>left</code>
     * @return a new {@link Guard} that compares <code>left</code> less than
     *         <code>right</code>
     */
    public static IGuard lessThanGuard(final Expression left,
	    final Expression right) {
	final IGuard guard = new Guard(new LessThan(left, right));

	return guard;
    }

    /**
     * Create a less than operator.
     * 
     * <pre>
     * left &lt; right
     * </pre>
     * 
     * @param left
     *            the left operand {@link Expression}
     * @param right
     *            the right operand {@link Expression}
     * @return a new {@link LessThan} that compares <code>left</code> less than
     *         <code>right</code>
     */
    public static LessThan lessThanOperator(final Expression left,
	    final Expression right) {
	final LessThan operator = new LessThan(left, right);

	return operator;
    }

    /**
     * Create a less than zero operator.
     * 
     * <pre>
     * expression &lt; 0
     * </pre>
     * 
     * @param expression
     *            the left operand {@link Expression}
     * @return a new {@link LessThan} that compares <code>expression</code> less
     *         than <code>0</code>
     */
    public static LessThan lessThanZeroOperator(final Expression expression) {
	final IntLiteral zeroLiteral = KeYJavaASTFactory.zeroLiteral();
	final LessThan operator = KeYJavaASTFactory.lessThanOperator(
		expression, zeroLiteral);

	return operator;
    }

    /**
     * Create a condition that compares a variable and an array length using the
     * less than operator.
     * 
     * <pre>
     * variable &lt; array.length
     * </pre>
     * 
     * @param model
     *            the {@link JavaInfo} to retrieve the array super class type,
     *            which holds the length attribute, from
     * @param variable
     *            the {@link ProgramVariable} to be compared less than
     *            <code>array</code>'s length
     * @param array
     *            the {@link ReferencePrefix} whose length attribute is accessed
     * @return a new {@link Guard} that compares <code>variable</code> less than
     *         <code>array</code>'s length
     */
    public static IGuard lessThanArrayLengthGuard(final JavaInfo model,
	    final ProgramVariable variable, final ReferencePrefix array) {
	final FieldReference length = KeYJavaASTFactory.arrayLength(model,
		array);
	final IGuard guard = KeYJavaASTFactory.lessThanGuard(variable, length);

	return guard;
    }

    /**
     * Create a list of loop updates that consists of a single expression.
     * 
     * <pre>
     * update
     * </pre>
     * 
     * @param update
     *            the single update {@link Expression}
     * @return a new {@link ForUpdates} that consists of <code>update</code>
     *         only
     */
    public static IForUpdates forUpdates(final Expression update) {
	final IForUpdates forUpdates = new ForUpdates(
		new ImmutableArray<Expression>(update));

	return forUpdates;
    }

    /**
     * Create a loop update expression that post increments a given variable.
     * 
     * <pre>
     * variable++
     * </pre>
     * 
     * @param variable
     *            the {@link ProgramVariable} to be post incremented during the
     *            loop updates
     * @return a new {@link ForUpdates} that consists of the post increment of
     *         <code>variable</code>
     */
    public static IForUpdates postIncrementForUpdates(
	    final ProgramVariable variable) {
	final Expression update = new PostIncrement(variable);
	final IForUpdates forUpdates = KeYJavaASTFactory.forUpdates(update);

	return forUpdates;
    }

    /**
     * Create an array field access with a single index.
     * 
     * <pre>
     * array[index]
     * </pre>
     * 
     * @param array
     *            the {@link ReferencePrefix} to be accessed
     * @param index
     *            the array access index {@link Expression}
     * @return a new {@link ArrayReference} for access of <code>array</code> at
     *         <code>index</code>
     */
    public static ArrayReference arrayFieldAccess(final ReferencePrefix array,
	    final Expression index) {
	final Expression[] indices = new Expression[] { index };
	final ArrayReference access = new ArrayReference(array, indices);

	return access;
    }

    /**
     * Create a block from an arbitrary number of statements.
     * 
     * @param statements
     *            the block statements as {@link ExtList}
     * @return a new {@link StatementBlock} consisting of
     *         <code>statements</code>
     */
    public static StatementBlock block(final ExtList statements) {
	final StatementBlock block = new StatementBlock(statements);

	return block;
    }

    /**
     * Create a block from an arbitrary number of statements.
     * 
     * <pre>
     * {
     *   statements;
     * }
     * </pre>
     * 
     * @param statements
     *            the {@link Statement}s to appear in the block
     * @return a new {@link StatementBlock} that consists of the given
     *         <code>statements</code> in the very same order
     */
    public static StatementBlock block(final Statement... statements) {
	final StatementBlock block = new StatementBlock(statements);

	return block;
    }

    /**
     * Create a block from an arbitrary number of statements.
     * 
     * <pre>
     * {
     *   statements;
     * }
     * </pre>
     * 
     * @param statements
     *            the {@link Statement}s to appear in the block
     * @return a new {@link StatementBlock} that consists of the given
     *         <code>statements</code> in the very same order
     */
    public static StatementBlock block(final List<Statement> statements) {
	final Statement[] s = new Statement[statements.size()];
	final StatementBlock block = KeYJavaASTFactory.block(statements
		.toArray(s));

	return block;
    }

    /**
     * Create a for loop.
     * 
     * @param parameters
     *            the loop definition parameters (initializer, guard, updates,
     *            body) as {@link ExtList}
     * @return a new {@link For} as defined by <code>parameters</code>
     */
    public static For forLoop(final ExtList parameters) {
	final For loop = new For(parameters);

	return loop;
    }

    /**
     * Create a for loop from the loop definition and an arbitrary number of
     * body statements.
     * 
     * <pre>
     * for (init; guard; updates) {
     *    statements;
     * }
     * </pre>
     * 
     * @param init
     *            the {@link ILoopInit} loop initializations
     * @param guard
     *            the {@link IGuard} loop condition
     * @param updates
     *            the {@link IForUpdates} loop updates
     * @param statements
     *            the body {@link Statement}s
     * @return a new {@link For} with initializers <code>init</code>, condition
     *         <code>guard</code>, updates <code>updates</code> and body
     *         <code>statements</code>
     */
    public static For forLoop(final ILoopInit init, final IGuard guard,
	    final IForUpdates updates, final Statement... statements) {
	final StatementBlock body = KeYJavaASTFactory.block(statements);

	return new For(init, guard, updates, body);
    }

    /**
     * Create a for loop with no initializer.
     * 
     * <pre>
     * for (; guard; updates)
     *     body
     * </pre>
     * 
     * @param guard
     *            the {@link IGuard} loop condition
     * @param updates
     *            the {@link IForUpdates} loop updates
     * @param body
     *            the body {@link Statement}
     * @return a new {@link For} with condition <code>guard</code>, updates
     *         <code>updates</code> and body <code>body</code>
     */
    public static For forLoop(final IGuard guard, final IForUpdates updates,
	    final Statement body) {
	final For loop = KeYJavaASTFactory.forLoop(null, guard, updates, body);

	return loop;
    }

    /**
     * Create a for loop with no initializer.
     * 
     * <pre>
     * for (; guard; updates)
     *     body
     * </pre>
     * 
     * @param guard
     *            the {@link IGuard} loop condition
     * @param updates
     *            the {@link IForUpdates} loop updates
     * @param body
     *            the body {@link Statement}s
     * @return a new {@link For} with condition <code>guard</code>, updates
     *         <code>updates</code> and body <code>body</code>
     */
    public static For forLoop(final IGuard guard, final IForUpdates updates,
	    final Statement[] body) {
	final For loop = KeYJavaASTFactory.forLoop(null, guard, updates, body);

	return loop;
    }

    /**
     * Create a statement that assigns an array element to a variable.
     * 
     * <pre>
     * variable = array[index];
     * </pre>
     * 
     * @param variable
     *            the {@link ProgramVariable} to be assigned to
     * @param array
     *            the array {@link ReferencePrefix} to be accessed
     * @param index
     *            the array access index {@link Expression}
     * @return a new {@link CopyAssignment} of <code>array</code> element at
     *         <code>index</code> to <code>variable</code>
     */
    public static CopyAssignment assignArrayField(
	    final ProgramVariable variable, final ReferencePrefix array,
	    final Expression index) {
	final ArrayReference element = KeYJavaASTFactory.arrayFieldAccess(
		array, index);
	final CopyAssignment assignment = KeYJavaASTFactory.assign(variable,
		element);

	return assignment;
    }

    /**
     * Create a local variable declaration without initialization.
     * 
     * @param parameters
     *            the declaration parameters (modifiers, type reference,
     *            variable specifications) as {@link ExtList}
     * @return a new {@link LocalVariableDeclaration} as defined by
     *         <code>parameters</code>
     */
    public static LocalVariableDeclaration declare(final ExtList parameters) {
	final LocalVariableDeclaration declaration = new LocalVariableDeclaration(
		parameters);

	return declaration;
    }

    /**
     * Create a local variable declaration without initialization.
     * 
     * <pre>
     * type variable;
     * </pre>
     * 
     * where <code>type</code> is <code>variable</code>'s {@link KeYJavaType} as
     * it is returned by {@link IProgramVariable#getKeYJavaType()}.
     * 
     * @param variable
     *            the named and typed {@link IProgramVariable} to be declared
     * @return a new {@link LocalVariableDeclaration} of <code>variable</code>
     */
    public static LocalVariableDeclaration declare(
	    final IProgramVariable variable) {
	final LocalVariableDeclaration declaration = KeYJavaASTFactory.declare(
		variable, (Expression) null);

	return declaration;
    }

    /**
     * Create a local variable declaration.
     * 
     * <pre>
     * type variable = init;
     * </pre>
     * 
     * where <code>type</code> is <code>variable</code>'s {@link KeYJavaType} as
     * it is returned by {@link IProgramVariable#getKeYJavaType()}.
     * 
     * @param variable
     *            the named and typed {@link IProgramVariable} to be declared
     * @param init
     *            the {@link Expression} <code>variable</code> is initialized
     *            with
     * @return a new {@link LocalVariableDeclaration} of <code>variable</code>
     */
    public static LocalVariableDeclaration declare(
	    final IProgramVariable variable, final Expression init) {
	final KeYJavaType type = variable.getKeYJavaType();
	final LocalVariableDeclaration declaration = KeYJavaASTFactory.declare(
		variable, init, type);

	return declaration;
    }

    /**
     * Create a local variable declaration with a single modifier.
     * 
     * <pre>
     * modifier type variable = init;
     * </pre>
     * 
     * @param modifier
     *            the {@link Modifier}
     * @param variable
     *            the named and typed {@link IProgramVariable} to be declared
     * @param init
     *            the {@link Expression} <code>variable</code> is initialized
     *            with
     * @param type
     *            the static {@link KeYJavaType} of <code>variable</code>
     * @return a new {@link LocalVariableDeclaration} of <code>variable</code>
     *         with static type <code>type</code> and initial value
     *         <code>init</code>
     */
    public static LocalVariableDeclaration declare(final Modifier modifier,
	    final IProgramVariable variable, final Expression init,
	    final KeYJavaType type) {
	final ImmutableArray<Modifier> modifiers = new ImmutableArray<Modifier>(
		modifier);
	final LocalVariableDeclaration declaration = KeYJavaASTFactory.declare(
		modifiers, variable, init, type);

	return declaration;
    }

    /**
     * Create a local variable declaration with an arbitrary number of
     * modifiers.
     * 
     * <pre>
     * modifiers type variable = init;
     * </pre>
     * 
     * @param modifiers
     *            the {@link Modifier}s
     * @param variable
     *            the named and typed {@link IProgramVariable} to be declared
     * @param init
     *            the {@link Expression} <code>variable</code> is initialized
     *            with
     * @param type
     *            the static {@link KeYJavaType} of <code>variable</code>
     * @return a new {@link LocalVariableDeclaration} of <code>variable</code>
     *         with static type <code>type</code> and initial value
     *         <code>init</code>
     */
    public static LocalVariableDeclaration declare(final Modifier[] modifiers,
	    final IProgramVariable variable, final Expression init,
	    final KeYJavaType type) {
	final ImmutableArray<Modifier> m = new ImmutableArray<Modifier>(
		modifiers);
	final LocalVariableDeclaration declaration = KeYJavaASTFactory.declare(
		m, variable, init, type);

	return declaration;
    }

    /**
     * Create a local variable declaration with an arbitrary number of
     * modifiers.
     * 
     * <pre>
     * modifiers type variable = init;
     * </pre>
     * 
     * @param modifiers
     *            the {@link Modifier}s
     * @param variable
     *            the named and typed {@link IProgramVariable} to be declared
     * @param init
     *            the {@link Expression} <code>variable</code> is initialized
     *            with
     * @param type
     *            the static {@link KeYJavaType} of <code>variable</code>
     * @return a new {@link LocalVariableDeclaration} of <code>variable</code>
     *         with static type <code>type</code> and initial value
     *         <code>init</code>
     */
    public static LocalVariableDeclaration declare(
	    final ImmutableArray<Modifier> modifiers,
	    final IProgramVariable variable, final Expression init,
	    final KeYJavaType type) {
	final TypeRef typeRef = new TypeRef(type);
	final LocalVariableDeclaration declaration = KeYJavaASTFactory.declare(
		modifiers, variable, init, typeRef);

	return declaration;
    }

    /**
     * Create a local variable declaration with an arbitrary number of
     * modifiers.
     * 
     * <pre>
     * modifiers typeRef variable = init;
     * </pre>
     * 
     * @param modifiers
     *            the {@link Modifier}s
     * @param variable
     *            the named and typed {@link IProgramVariable} to be declared
     * @param init
     *            the {@link Expression} <code>variable</code> is initialized
     *            with
     * @param typeRef
     *            the static {@link TypeRef} of <code>variable</code>
     * @return a new {@link LocalVariableDeclaration} of <code>variable</code>
     *         with static type <code>typeRef</code> and initial value
     *         <code>init</code>
     */
    public static LocalVariableDeclaration declare(
	    final ImmutableArray<Modifier> modifiers,
	    final IProgramVariable variable, final Expression init,
	    final TypeReference typeRef) {
	final VariableSpecification varSpec = KeYJavaASTFactory
		.variableSpecification(variable, init, typeRef.getKeYJavaType());
	final LocalVariableDeclaration declaration = KeYJavaASTFactory.declare(
		modifiers, typeRef, varSpec);

	return declaration;
    }

    /**
     * Create a local variable declaration.
     * 
     * <pre>
     * modifiers typeRef specification
     * </pre>
     * 
     * @param modifiers
     *            the {@link Modifier}s
     * @param typeRef
     *            the static {@link TypeRef} of the variable to be declared
     * @param specification
     *            the {@link VariableSpecification} of the variable to be
     *            declared
     * @return a new {@link LocalVariableDeclaration} of the variable specified
     *         by <code>specification</code> with static type
     *         <code>typeRef</code>
     */
    public static LocalVariableDeclaration declare(
	    final ImmutableArray<Modifier> modifiers,
	    final TypeReference typeRef,
	    final VariableSpecification specification) {
	final LocalVariableDeclaration declaration = new LocalVariableDeclaration(
		modifiers, typeRef, specification);

	return declaration;
    }

    /**
     * Create local variable declarations.
     * 
     * <pre>
     * modifiers typeRef specification{1}, ...
     * </pre>
     * 
     * @param modifiers
     *            the {@link Modifier}s
     * @param typeRef
     *            the static {@link TypeRef} of the variable to be declared
     * @param specifications
     *            the {@link VariableSpecification}s of the variables to be
     *            declared
     * @return a new {@link LocalVariableDeclaration} of the variables specified
     *         by <code>specifications</code> with static type
     *         <code>typeRef</code>
     */
    public static LocalVariableDeclaration declare(
	    final ImmutableArray<Modifier> modifiers,
	    final TypeReference typeRef,
	    final VariableSpecification[] specifications) {
	final LocalVariableDeclaration declaration = new LocalVariableDeclaration(
		modifiers, typeRef, specifications);

	return declaration;
    }

    /**
     * Create a method call.
     * 
     * <pre>
     * reference.name(args);
     * </pre>
     * 
     * @param reference
     *            the {@link ReferencePrefix} the method is called on
     * @param name
     *            the method's name {@link String}
     * @param args
     *            the argument {@link Expression}s to be passed to the method
     * @return a new {@link MethodReference} for call of method
     *         <code>name</code> on <code>reference</code> with arguments
     *         <code>args</code>
     */
    public static MethodReference methodCall(final ReferencePrefix reference,
	    final String name, final ImmutableArray<? extends Expression> args) {
	final ProgramElementName method = new ProgramElementName(name);
	final MethodReference call = KeYJavaASTFactory.methodCall(reference,
		method, args);

	return call;
    }

    /**
     * Create a method call on a type.
     * 
     * <pre>
     * type.name(args);
     * </pre>
     * 
     * @param type
     *            the {@link KeYJavaType} the method is called on
     * @param name
     *            the method's name {@link String}
     * @param args
     *            the argument {@link Expression}s to be passed to the method
     * @return a new {@link MethodReference} for call of method
     *         <code>name</code> on <code>type</code> with arguments
     *         <code>args</code>
     */
    public static MethodReference methodCall(final KeYJavaType type,
	    final String name, final ImmutableArray<? extends Expression> args) {
	final TypeReference typeRef = new TypeRef(type);
	final MethodReference call = KeYJavaASTFactory.methodCall(typeRef,
		name, args);

	return call;
    }

    /**
     * Create a method call on a type.
     * 
     * <pre>
     * type.name(args);
     * </pre>
     * 
     * @param type
     *            the {@link KeYJavaType} the method is called on
     * @param name
     *            the method's name {@link String}
     * @param args
     *            the argument {@link Expression}s to be passed to the method
     * @return a new {@link MethodReference} for call of method
     *         <code>name</code> on <code>type</code> with arguments
     *         <code>args</code>
     */
    public static MethodReference methodCall(final KeYJavaType type,
	    final String name, final Expression... args) {
	final TypeReference typeRef = new TypeRef(type);
	final MethodReference call = KeYJavaASTFactory.methodCall(typeRef,
		name, args);

	return call;
    }

    /**
     * Create a method call on a type with no arguments.
     * 
     * <pre>
     * type.name();
     * </pre>
     * 
     * @param type
     *            the {@link KeYJavaType} the method is called on
     * @param name
     *            the method's name {@link String}
     * @return a new {@link MethodReference} for call of method
     *         <code>name</code> on <code>type</code> with arguments
     *         <code>args</code>
     */
    public static MethodReference methodCall(final KeYJavaType type,
	    final String name) {
	final ImmutableArray<? extends Expression> args = new ImmutableArray<Expression>();
	final MethodReference call = KeYJavaASTFactory.methodCall(type, name,
		args);

	return call;
    }

    /**
     * Create a method call with no arguments.
     * 
     * <pre>
     * reference.name();
     * </pre>
     * 
     * @param reference
     *            the {@link ReferencePrefix} the method is called on
     * @param name
     *            the method's name {@link String}
     * @return a new {@link MethodReference} for call of method
     *         <code>name</code> on <code>reference</code> with no arguments
     */
    public static MethodReference methodCall(final ReferencePrefix reference,
	    final String name) {
	final ImmutableArray<Expression> args = new ImmutableArray<Expression>();
	final MethodReference call = KeYJavaASTFactory.methodCall(reference,
		name, args);

	return call;
    }

    /**
     * Create a method call.
     * 
     * <pre>
     * reference.name(args);
     * </pre>
     * 
     * @param reference
     *            the {@link ReferencePrefix} the method is called on
     * @param name
     *            the method's name {@link String}
     * @param args
     *            the argument {@link Expression}s to be passed to the method
     * @return a new {@link MethodReference} for call of method
     *         <code>name</code> on <code>reference</code> with arguments
     *         <code>args</code>
     */
    public static MethodReference methodCall(final ReferencePrefix reference,
	    final String name, final Expression... args) {
	final ImmutableArray<? extends Expression> a = new ImmutableArray<Expression>(
		args);
	final MethodReference call = KeYJavaASTFactory.methodCall(reference,
		name, a);

	return call;
    }

    /**
     * Create a method call.
     * 
     * <pre>
     * reference.name(args);
     * </pre>
     * 
     * @param reference
     *            the {@link ReferencePrefix} the method is called on
     * @param name
     *            the {@link MethodName}
     * @param args
     *            the argument {@link Expression}s to be passed to the method
     * @return a new {@link MethodReference} for call of method
     *         <code>name</code> on <code>reference</code> with arguments
     *         <code>args</code>
     */
    public static MethodReference methodCall(final ReferencePrefix reference,
	    final MethodName name, final Expression... args) {
	final ImmutableArray<Expression> a = new ImmutableArray<Expression>(
		args);
	final MethodReference call = KeYJavaASTFactory.methodCall(reference,
		name, a);

	return call;
    }

    /**
     * Create a method call.
     * 
     * <pre>
     * reference.name(args);
     * </pre>
     * 
     * @param reference
     *            the {@link ReferencePrefix} the method is called on
     * @param name
     *            the {@link MethodName}
     * @param args
     *            the argument {@link Expression}s to be passed to the method
     * @return a new {@link MethodReference} for call of method
     *         <code>name</code> on <code>reference</code> with arguments
     *         <code>args</code>
     */
    public static MethodReference methodCall(final ReferencePrefix reference,
	    final MethodName name,
	    final ImmutableArray<? extends Expression> args) {
	final MethodReference call = new MethodReference(args, name, reference);

	return call;
    }

    /**
     * Create a field access.
     * 
     * <pre>
     * (expression).name
     * </pre>
     * 
     * @param services
     *            the {@link Services} to determine both <code>expression</code>
     *            's {@link KeYJavaType} and the {@link ProgramVariable}
     *            corresponding to the field <code>name</code>
     * @param name
     *            the to be accessed field's name {@link String}
     * @param expression
     *            the {@link Expression} on which the field is accessed
     * @param context
     *            the {@link ExecutionContext}, which is needed to determine
     *            <code>expression</code>'s <code>KeYJavaType</code>
     * @return a new {@link FieldReference} of field <code>name</code> on
     *         <code>expression</code>
     */
    public static FieldReference fieldReference(final Services services,
	    final String name, final Expression expression,
	    final ExecutionContext context) {
	final KeYJavaType classType = expression.getKeYJavaType(services,
		context);
	final ProgramVariable field = services.getJavaInfo().getAttribute(name,
		classType);
	final FieldReference reference = KeYJavaASTFactory.fieldReference(
		new ParenthesizedExpression(expression), field);

	return reference;
    }

    /**
     * Create a field access.
     * 
     * <pre>
     * prefix.field
     * </pre>
     * 
     * @param prefix
     *            the {@link ReferencePrefix} on which <code>field</code> is
     *            accessed
     * @param field
     *            the {@link ProgramVariable} to be accessed
     * @return a new {@link FieldReference} of <code>field</code> on
     *         <code>prefix</code>
     */
    public static FieldReference fieldReference(final ReferencePrefix prefix,
	    final ProgramVariable field) {
	final FieldReference reference = new FieldReference(field, prefix);

	return reference;
    }

    /**
     * Create a finally block.
     * 
     * @param parameters
     *            the finally block parameters (body) as {@link ExtList}
     * @return a new {@link Finally} as defined by <code>parameters</code>
     */
    public static Finally finallyBlock(final ExtList parameters) {
	final Finally block = new Finally(parameters);

	return block;
    }

    /**
     * Create a finally block.
     * 
     * <pre>
     * finally
     *     statement
     * </pre>
     * 
     * @param statement
     *            the {@link Statement} to be executed
     * @return a new {@link Finally} block consisting of <code>statement</code>
     *         solely
     */
    public static Finally finallyBlock(final Statement statement) {
	final StatementBlock body = KeYJavaASTFactory.block(statement);
	final Finally block = KeYJavaASTFactory.finallyBlock(body);

	return block;
    }

    /**
     * Create a finally block.
     * 
     * <pre>
     * finally {
     *     statements
     * }
     * </pre>
     * 
     * @param statements
     *            the {@link Statement}s to be executed
     * @return a new {@link Finally} block consisting of <code>statements</code>
     *         solely
     */
    public static Finally finallyBlock(final Statement[] statements) {
	final StatementBlock body = KeYJavaASTFactory.block(statements);
	final Finally block = KeYJavaASTFactory.finallyBlock(body);

	return block;
    }

    /**
     * Create a finally block.
     * 
     * <pre>
     * finally
     *     body
     * </pre>
     * 
     * @param body
     *            the {@link StatementBlock} to be executed
     * @return a new {@link Finally} block consisting of <code>body</code>
     *         solely
     */
    public static Finally finallyBlock(final StatementBlock body) {
	final Finally block = new Finally(body);

	return block;
    }

    /**
     * Create a local array variable declaration with an arbitrary number of
     * modifiers.
     * 
     * <pre>
     * modifiers typePrefix.baseType[] variable = init;
     * </pre>
     * 
     * @param modifiers
     *            the {@link Modifiers}
     * @param variable
     *            the named and typed {@link IProgramVariable} to be declared
     * @param init
     *            the {@link Expression} <code>variable</code> is initialized
     *            with
     * @param typeName
     *            the type's {@link ProgramElementName}
     * @param dimensions
     *            the type's dimensions
     * @param typePrefix
     *            the type's {@link ReferencePrefix}
     * @param baseType
     *            the base {@link KeYJavaType}
     * @return a new {@link LocalVariableDeclaration} of <code>variable</code>
     *         with static type <code>baseType[dimensions]</code> and initial
     *         value <code>init</code>
     */
    public static ProgramElement declare(
	    final ImmutableArray<Modifier> modifiers,
	    final IProgramVariable variable, final Expression init,
	    final ProgramElementName typeName, final int dimensions,
	    final ReferencePrefix typePrefix, final KeYJavaType baseType) {
	final TypeRef typeRef = new TypeRef(typeName, dimensions, typePrefix,
		baseType);
	final LocalVariableDeclaration declaration = KeYJavaASTFactory.declare(
		modifiers, variable, init, typeRef);

	return declaration;
    }

    /**
     * Create a method body shortcut.
     * 
     * Note that <code>classType</code> is also used as visibility context when
     * looking for <code>methodName</code> in its definition.
     * 
     * @param model
     *            the {@link JavaInfo} that contains
     *            <code>classType.methodName</code>
     * @param result
     *            the {@link ProgramVariable} the return value is assigned to or
     *            <code>null</code>
     * @param reference
     *            the {@link ReferencePrefix} invocation target
     * @param classType
     *            the {@link KeYJavaType} in which the method is declared
     * @param methodName
     *            the method's {@link String} name
     * @param arguments
     *            the <code>ProgramVariable</code> and their static types the
     *            method is called with
     * @return a new {@link MethodBodyStatement} for
     *         <code>classType.methodName</code> when called with
     *         <code>arguments</code> or <code>null</code> when the former is
     *         not defined
     */
    public static MethodBodyStatement methodBody(final JavaInfo model,
	    final ProgramVariable result, final ReferencePrefix reference,
	    final KeYJavaType classType, final String methodName,
	    final ProgramVariable[] arguments) {
	final IProgramMethod method = model.getProgramMethod(classType,
		methodName, arguments, classType);
	MethodBodyStatement methodBody = null;

	if (method != null) {
	    methodBody = KeYJavaASTFactory.methodBody(result, reference,
		    method, arguments);
	}

	return methodBody;
    }

    /**
     * Create a method body shortcut.
     * 
     * @param result
     *            the {@link ProgramVariable} the return value is assigned to or
     *            <code>null</code>
     * @param reference
     *            the {@link ReferencePrefix} invocation target
     * @param method
     *            the {@link IProgramMethod} reference
     * @param arguments
     *            the <code>Expression</code>s and their static types the method
     *            is called with
     * @return a new {@link MethodBodyStatement} for <code>method</code> when
     *         called with <code>arguments</code>
     */
    public static MethodBodyStatement methodBody(final ProgramVariable result,
	    final ReferencePrefix reference, final IProgramMethod method,
	    final Expression[] arguments) {
	final MethodBodyStatement methodBody = KeYJavaASTFactory.methodBody(
		result, reference, method, new ImmutableArray<Expression>(
			arguments));

	return methodBody;
    }

    /**
     * Create a method body shortcut.
     * 
     * @param result
     *            the {@link ProgramVariable} the return value is assigned to or
     *            <code>null</code>
     * @param reference
     *            the {@link ReferencePrefix} invocation target
     * @param method
     *            the {@link IProgramMethod} reference
     * @param arguments
     *            the <code>Expression</code>s and their static types the method
     *            is called with
     * @return a new {@link MethodBodyStatement} for <code>method</code> when
     *         called with <code>arguments</code>
     */
    public static MethodBodyStatement methodBody(final ProgramVariable result,
	    final ReferencePrefix reference, final IProgramMethod method,
	    final ImmutableArray<Expression> arguments) {
	final MethodBodyStatement methodBody = new MethodBodyStatement(method,
		reference, result, arguments);

	return methodBody;
    }

    /**
     * Create a method call substitution.
     * 
     * @param executionContext
     *            the <code>block</code>'s {@link IExecutionContext}
     * @param block
     *            the {@link StatementBlock} to be put in <code>executionContext</code>
     * @return a new {@link MethodFrame} that associates <code>block</code> with
     *         <code>executionContext</code>
     */
    public static MethodFrame methodFrame(
	    final IExecutionContext executionContext, final StatementBlock block) {
	final MethodFrame frame = KeYJavaASTFactory.methodFrame(null,
		executionContext, block);

	return frame;
    }

    /**
     * Create a method call substitution at a specific source position.
     * 
     * @param executionContext
     *            the <code>block</code>'s {@link IExecutionContext}
     * @param block
     *            the {@link StatementBlock} to be put in
     *            <code>executionContext</code>
     * @param position
     *            the new source element's {@link PositionInfo}
     * @return a new {@link MethodFrame} that associates <code>block</code> with
     *         <code>executionContext</code> and positions it at
     *         <code>position</code>
     */
    public static MethodFrame methodFrame(
	    final IExecutionContext executionContext,
	    final StatementBlock block, final PositionInfo position) {
	final MethodFrame frame = KeYJavaASTFactory.methodFrame(null,
		executionContext, block, position);

	return frame;
    }

    /**
     * Create a method call substitution with a return value assignment.
     * 
     * @param result
     *            the {@link IProgramVariable} <code>block</code>'s return value
     *            is assigned to
     * @param executionContext
     *            the <code>block</code>'s {@link IExecutionContext}
     * @param block
     *            the {@link StatementBlock} to be put in
     *            <code>executionContext</code>
     * @return a new {@link MethodFrame} that associates <code>block</code> with
     *         <code>executionContext</code>
     */
    public static MethodFrame methodFrame(final IProgramVariable result,
	    final IExecutionContext executionContext, final StatementBlock block) {
	final MethodFrame frame = new MethodFrame(result, executionContext,
		block);

	return frame;
    }

    /**
     * Create a method call substitution with a return value assignment at a
     * specific source position.
     * 
     * @param result
     *            the {@link IProgramVariable} <code>block</code>'s return value
     *            is assigned to
     * @param executionContext
     *            the <code>block</code>'s {@link IExecutionContext}
     * @param block
     *            the {@link StatementBlock} to be put in
     *            <code>executionContext</code>
     * @param position
     *            the new source element's {@link PositionInfo}
     * @return a new {@link MethodFrame} that associates <code>block</code> with
     *         <code>executionContext</code> and positions it at
     *         <code>position</code>
     */
    public static MethodFrame methodFrame(final IProgramVariable result,
	    final IExecutionContext executionContext,
	    final StatementBlock block, final PositionInfo position) {
	final MethodFrame frame = new MethodFrame(result, executionContext,
		block, position);

	return frame;
    }

    /**
     * Create an integer literal.
     * 
     * @param value
     *            the {@link Integer} to be turned into an literal
     * @return a new {@link IntLiteral} representing <code>value</code>
     */
    public static IntLiteral intLiteral(final Integer value) {
	final IntLiteral literal = new IntLiteral(value);

	return literal;
    }

    /**
     * Create a labeled statement.
     * 
     * @param parameters
     *            the parameters (statement) as {@link ExtList}
     * @param label
     *            the {@link Label}
     * @param position
     *            the new source element's {@link PositionInfo}
     * @return a new {@link LabeledStatement} as defined by
     *         <code>parameters</code> and <code>label</code>
     */
    public static LabeledStatement labeledStatement(final ExtList parameters,
	    final Label label, final PositionInfo position) {
	final LabeledStatement statement = new LabeledStatement(parameters,
		label, position);

	return statement;
    }

    /**
     * Create a labeled statement.
     * 
     * <pre>
     * label: statement
     * </pre>
     * 
     * @param label
     *            the {@link Label}
     * @param statement
     *            the {@link Statement} to be labeled
     * @return a new {@link LabeledStatement} that adds <code>label</code> to
     *         <code>statement</code>
     */
    public static LabeledStatement labeledStatement(final Label label,
	    final Statement statement) {
	final LabeledStatement labeled = new LabeledStatement(label, statement);

	return labeled;
    }

    /**
     * Create a labeled block of statements.
     * 
     * <pre>
     * label: {
     *     statements
     * }
     * </pre>
     * 
     * @param label
     *            the {@link Label}
     * @param statements
     *            the {@link Statement}s to be labeled
     * @return a new {@link LabeledStatement} that adds <code>label</code> to
     *         <code>statements</code>
     */
    public static Statement labeledStatement(final Label label,
	    final Statement[] statements) {
	final StatementBlock block = KeYJavaASTFactory.block(statements);
	final LabeledStatement labeled = KeYJavaASTFactory.labeledStatement(
		label, block);

	return labeled;
    }

    /**
     * Create an array instantiation.
     * 
     * <pre>
     * new typeRef[sizes{1}]...[sizes{dimensions}] initializer
     * </pre>
     * 
     * @param sizes
     *            the size {@link Expression}s for each dimension
     * @param typeRef
     *            the static array base type
     * @param keyJavaType
     *            the array element type
     * @param initializer
     *            the {@link ArrayInitializer}
     * @param dimensions
     *            the number of dimensions
     * @return a new {@link NewArray} for the instantiation of an array of base
     *         type <code>typeRef</code> with <code>dimensions</code> dimensions
     */
    public static NewArray newArray(final TypeReference typeRef,
	    final int dimensions, final Expression[] sizes,
	    final ArrayInitializer initializer, final KeYJavaType keyJavaType) {
	final NewArray newArray = new NewArray(sizes, typeRef, keyJavaType,
		initializer, dimensions);

	return newArray;
    }

    /**
     * Create an array instantiation.
     * 
     * <pre>
     * new typeRef[sizes{1}]...[sizes{dimensions}]
     * </pre>
     * 
     * @param typeRef
     *            the static array base type
     * @param dimensions
     *            the number of dimensions
     * @param sizes
     *            the size {@link Expression}s for each dimension
     * @param keyJavaType
     *            the array element type
     * @return a new {@link NewArray} for the instantiation of an array of base
     *         type <code>typeRef</code> with <code>dimensions</code> dimensions
     */
    public static NewArray newArray(final TypeReference typeRef,
	    final int dimensions, final Expression[] sizes,
	    final KeYJavaType keyJavaType) {
	final NewArray newArray = KeYJavaASTFactory.newArray(typeRef,
		dimensions, sizes, null, keyJavaType);

	return newArray;
    }

    /**
     * Create an array instantiation.
     * 
     * <pre>
     * new typeRef[size]
     * </pre>
     * 
     * @param typeRef
     *            the static array base type
     * @param dimensions
     *            the number of dimensions
     * @param size
     *            the size {@link Expression} for the first dimension
     * @param keyJavaType
     *            the array element type
     * @return a new {@link NewArray} for the instantiation of an array of base
     *         type <code>typeRef</code> with <code>dimensions</code> dimensions
     */
    public static NewArray newArray(final TypeReference typeRef,
	    final int dimensions, final Expression size,
	    final KeYJavaType keyJavaType) {
	final Expression[] sizes = new Expression[] { size };
	final NewArray newArray = KeYJavaASTFactory.newArray(typeRef,
		dimensions, sizes, null, keyJavaType);

	return newArray;
    }

    /**
     * Create an array instantiation.
     * 
     * <pre>
     * new typeRef[]...[] initializer
     * </pre>
     * 
     * @param typeRef
     *            the static array base type
     * @param keyJavaType
     *            the array element type
     * @param initializer
     *            the {@link ArrayInitializer}
     * @param dimensions
     *            the number of dimensions
     * @return a new {@link NewArray} for the instantiation of an array of base
     *         type <code>typeRef</code> with <code>dimensions</code> dimensions
     */
    public static NewArray newArray(final TypeReference typeRef,
	    final int dimensions, final ArrayInitializer initializer,
	    final KeYJavaType keyJavaType) {
	final Expression[] sizes = new Expression[0];
	final NewArray newArray = KeYJavaASTFactory.newArray(typeRef,
		dimensions, sizes, initializer, keyJavaType);

	return newArray;
    }

    /**
     * Create an object allocation.
     * 
     * <pre>
     * new referencePrefix.typeReference(args)
     * </pre>
     * 
     * @param referencePrefix
     *            the <code>typeReference</code>'s {@link ReferencePrefix}
     * @param typeReference
     *            a {@link TypeReference} to the class type that is instantiated
     * @param args
     *            the {@link Expression} arguments to be passed to the
     *            constructor
     * @return a new {@link New} operator that allocates a new instance of
     *         <code>typeReference</code> parameterized with <code>args</code>
     */
    public static New newOperator(final ReferencePrefix referencePrefix,
	    final TypeReference typeReference, final Expression[] args) {
	final New operator = new New(args, typeReference, referencePrefix);

	return operator;
    }

    /**
     * Create an object allocation.
     * 
     * <pre>
     * new referencePrefix.type(args)
     * </pre>
     * 
     * @param referencePrefix
     *            the <code>type</code>'s {@link ReferencePrefix}
     * @param type
     *            the {@link KeYJavaType} to be instantiated
     * @param args
     *            the {@link Expression} arguments to be passed to the
     *            constructor
     * @return a new {@link New} operator that allocates a new instance of
     *         <code>type</code> parameterized with <code>args</code>
     */
    public static New newOperator(final ReferencePrefix referencePrefix,
	    final KeYJavaType type, final Expression[] args) {
	final TypeReference typeRef = new TypeRef(type);
	final New operator = KeYJavaASTFactory.newOperator(referencePrefix,
		typeRef, args);

	return operator;
    }

    /**
     * Create an object allocation without arguments.
     * 
     * <pre>
     * new referencePrefix.type()
     * </pre>
     * 
     * @param referencePrefix
     *            the <code>type</code>'s {@link ReferencePrefix}
     * @param type
     *            the {@link KeYJavaType} to be instantiated
     * @return a new {@link New} operator that allocates a new instance of
     *         <code>type</code>
     */
    public static New newOperator(final ReferencePrefix referencePrefix,
	    final KeYJavaType type) {
	final Expression[] args = new Expression[0];
	final New operator = KeYJavaASTFactory.newOperator(referencePrefix,
		type, args);

	return operator;
    }

    /**
     * Create an object allocation without arguments.
     * 
     * <pre>
     * new type()
     * </pre>
     * 
     * @param type
     *            the {@link KeYJavaType} to be instantiated
     * @return a new {@link New} operator that allocates a new instance of
     *         <code>type</code>
     */
    public static New newOperator(final KeYJavaType type) {
	final New operator = KeYJavaASTFactory.newOperator(null, type);

	return operator;
    }

    /**
     * Create an unequal operator.
     * 
     * <pre>
     * operands{1} != operands{2}
     * </pre>
     * 
     * @param operands
     *            the operands {@link ExtList}
     * @return a new {@link NotEquals} of <code>operands</code>
     */
    public static NotEquals notEqualsOperator(final ExtList operands) {
	final NotEquals operator = new NotEquals(operands);

	return operator;
    }

    /**
     * Create a call to the super constructor.
     * 
     * <pre>
     * super(args)
     * </pre>
     * 
     * @param referencePrefix
     *            the enclosing class type
     * @param args
     *            the {@link Expression} arguments to be passed to constructor
     * @return a new {@link SuperConstructorReference} parameterized with
     *         <code>args</code>
     */
    public static SuperConstructorReference superConstructor(
	    final ReferencePrefix referencePrefix, final Expression[] args) {
	final SuperConstructorReference constructor = new SuperConstructorReference(
		args);

	return constructor;
    }

    /**
     * Create a reference to <code>super</code>.
     * 
     * @return a new {@link SuperReference}
     */
    public static SuperReference superReference() {
	final SuperReference reference = new SuperReference();

	return reference;
    }

    /**
     * Create a switch block.
     * 
     * <pre>
     * switch (expression) {
     *     branches
     * }
     * </pre>
     * 
     * @param expression
     *            the to be evaluated {@link Expression}
     * @param branches
     *            the switch-case {@link Branch}es
     * @return a new {@link Switch} block that executes <code>branches</code>
     *         depending on the value of <code>expression</code>
     */
    public static Switch switchBlock(final Expression expression,
	    final Branch[] branches) {
	final Switch block = new Switch(expression, branches);

	return block;
    }

    /**
     * Create a switch block.
     * 
     * @param parameters
     *            the switch-case parameters (guard, body, branches) as
     *            {@link ExtList}
     * @return a new {@link Switch} as defined by <code>parameters</code>
     */
    public static Switch switchBlock(final ExtList parameters) {
	final Switch block = new Switch(parameters);

	return block;
    }

    /**
     * Create a synchronized block.
     * 
     * @param parameters
     *            the synchronized block parameters (monitor, body) as
     *            {@link ExtList}
     * @return a new {@link SynchronizedBlock} as defined by
     *         <code>parameters</code>
     */
    public static SynchronizedBlock synchronizedBlock(final ExtList parameters) {
	final SynchronizedBlock block = new SynchronizedBlock(parameters);

	return block;
    }

    /**
     * Create a then block.
     * 
     * @param parameters
     *            the then block parameters (body) as {@link ExtList}
     * @return a new {@link Then} as defined by <code>parameters</code>
     */
    public static Then thenBlock(final ExtList parameters) {
	final Then block = new Then(parameters);

	return block;
    }

    /**
     * Create a then block.
     * 
     * <pre>
     * then
     *     statement
     * </pre>
     * 
     * @param statement
     *            the to be executed {@link Statement}
     * @return a new {@link Then} block that consists of <code>statement</code>
     *         solely
     */
    public static Then thenBlock(final Statement statement) {
	final Then block = new Then(statement);

	return block;
    }

    /**
     * Create a then block.
     * 
     * <pre>
     * then {
     *     statements
     * }
     * </pre>
     * 
     * @param statements
     *            the to be executed {@link Statement}s
     * @return a new {@link Then} block that consists of <code>statements</code>
     *         solely
     */
    public static Then thenBlock(final Statement[] statements) {
	final StatementBlock statement = KeYJavaASTFactory.block(statements);
	final Then block = KeYJavaASTFactory.thenBlock(statement);

	return block;
    }

    /**
     * Create a call to a constructor of the current class.
     * 
     * <pre>
     * this(args)
     * </pre>
     * 
     * @param args
     *            the {@link Expression} arguments to be passed to constructor
     * @return a new {@link ThisConstructorReference} parameterized with
     *         <code>args</code>
     */
    public static ThisConstructorReference thisConstructor(
	    final Expression[] args) {
	final ThisConstructorReference constructor = new ThisConstructorReference(
		args);

	return constructor;
    }

    /**
     * Create a reference to <code>this</code>.
     * 
     * @return a new {@link ThisReference}
     */
    public static ThisReference thisReference() {
	final ThisReference reference = new ThisReference();

	return reference;
    }

    /**
     * Create a literal for the truth value <code>true</code>.
     * 
     * @return a {@link BooleanLiteral} that represents the value
     *         <code>true</code>
     */
    public static BooleanLiteral trueLiteral() {
	return BooleanLiteral.TRUE;
    }

    /**
     * Create a try block.
     * 
     * @param parameters
     *            the try-catch parameters (body, branches) as {@link ExtList}
     * @return a new {@link Try} as defined by <code>parameters</code>
     */
    public static Try tryBlock(final ExtList parameters) {
	final Try block = new Try(parameters);

	return block;
    }

    /**
     * Create a try block.
     * 
     * <pre>
     * try
     *     body
     * branches
     * </pre>
     * 
     * @param body
     *            the {@link StatementBlock} to be executed
     * @param branches
     *            the try-catch {@link Branch}es
     * @return a new {@link Try} block for the execution of
     *         <code>branches</code> depending on the events during the
     *         execution of <code>body</code>
     */
    public static Try tryBlock(final StatementBlock body,
	    final Branch[] branches) {
	final Try block = new Try(body, branches);

	return block;
    }

    /**
     * Create a try block.
     * 
     * <pre>
     * try
     *     statement
     * branches
     * </pre>
     * 
     * @param statement
     *            the {@link Statement} to be executed
     * @param branches
     *            the try-catch {@link Branch}es
     * @return a new {@link Try} block for the execution of
     *         <code>branches</code> depending on the events during the
     *         execution of <code>statement</code>
     */
    public static Try tryBlock(final Statement statement,
	    final Branch[] branches) {
	final StatementBlock body = KeYJavaASTFactory.block(statement);
	final Try tryBlock = KeYJavaASTFactory.tryBlock(body, branches);

	return tryBlock;
    }

    /**
     * Create a try block.
     * 
     * <pre>
     * try
     *     statement
     * branch
     * </pre>
     * 
     * @param statement
     *            the {@link Statement} to be executed
     * @param branches
     *            the try-catch {@link Branch}
     * @return a new {@link Try} block for the execution of <code>branch</code>
     *         depending on the events during the execution of
     *         <code>statement</code>
     */
    public static Try tryBlock(final Statement statement, final Branch branch) {
	final Branch[] branches = new Branch[] { branch };
	final Try tryBlock = KeYJavaASTFactory.tryBlock(statement, branches);

	return tryBlock;
    }

    /**
     * Create a type reference.
     * 
     * <pre>
     * type
     * </pre>
     * 
     * @param type
     *            the {@link KeYJavaType} to be referenced
     * @return a new {@link TypeRef} that references <code>type</code>
     */
    public static TypeRef typeRef(final KeYJavaType type) {
	final TypeRef typeRef = new TypeRef(type);

	return typeRef;
    }

    /**
     * Create a type reference.
     * 
     * <pre>
     * type[]...[]
     * </pre>
     * 
     * @param type
     *            the base {@link KeYJavaType}
     * @param dimensions
     *            the number of dimensions
     * @return a new {@link TypeRef} for <code>dimensions</code> dimensions of
     *         <code>type</code>
     */
    public static TypeRef typeRef(final KeYJavaType type, final int dimensions) {
	final TypeRef typeRef = new TypeRef(type, dimensions);

	return typeRef;
    }

    /**
     * Create a literal for the truth value <code>false</code>.
     * 
     * @return a {@link BooleanLiteral} that represents the value
     *         <code>true</code>
     */
    public static BooleanLiteral falseLiteral() {
	return BooleanLiteral.FALSE;
    }

    /**
     * Create a variable specification.
     * 
     * @param variable
     *            the {@link IProgramVariable} to be specified
     * @param dimensions
     *            the number of dimensions
     * @param initializer
     *            the initializer {@link Expression}
     * @param type
     *            the {@link Type}
     * @return a new {@link VariableSpecification} for <code>variable</code> of
     *         type <code>type[dimensions]</code>, initialized to
     *         <code>initializer</code>
     */
    public static VariableSpecification variableSpecification(
	    final IProgramVariable variable, final int dimensions,
	    final Expression initializer, final Type type) {
	final VariableSpecification specification = new VariableSpecification(
		variable, dimensions, initializer, type);

	return specification;
    }

    /**
     * Create a variable specification.
     * 
     * @param variable
     *            the {@link IProgramVariable} to be specified
     * @param initializer
     *            the initializer {@link Expression}
     * @param keyJavaType
     *            the {@link KeYJavaType}
     * @return a new {@link VariableSpecification} for <code>variable</code> of
     *         type <code>type</code>, initialized to <code>initializer</code>
     */
    public static VariableSpecification variableSpecification(
	    final IProgramVariable variable, final Expression initializer,
	    final KeYJavaType keyJavaType) {
	final VariableSpecification specification = new VariableSpecification(
		variable, initializer, keyJavaType);

	return specification;
    }

    /**
     * Create a literal for the integer zero.
     * 
     * <pre>
     * 0
     * </pre>
     * 
     * @return a new {@link IntLiteral} that represents the integer value
     *         <code>0</code>
     */
    public static IntLiteral zeroLiteral() {
	final IntLiteral literal = KeYJavaASTFactory.intLiteral(0);

	return literal;
    }
}