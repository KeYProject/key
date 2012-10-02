// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;

import java.util.List;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.ParenthesizedExpression;
import de.uka.ilkd.key.java.expression.literal.BooleanLiteral;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.Instanceof;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.expression.operator.New;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.java.reference.ArrayReference;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.MethodName;
import de.uka.ilkd.key.java.reference.MethodReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.SuperConstructorReference;
import de.uka.ilkd.key.java.reference.ThisConstructorReference;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.IProgramMethod;
import de.uka.ilkd.key.logic.op.IProgramVariable;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;


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
    public static Statement whileLoop(final Expression condition,
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
	return new If(guard, new Then(then));
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
     * Create a break statement.
     * 
     * @param l
     *            the break destination {@link Label}
     * @return a new {@link Break} with label <code>l</code>
     */
    public static Break breakStatement(Label l) {
	return new Break(l);
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
	return KeYJavaASTFactory.declare(variable, new IntLiteral(0), type);
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
	    final TypeRef typeRef) {
	final VariableSpecification varSpec = new VariableSpecification(
		variable, init, typeRef.getKeYJavaType());
	final LocalVariableDeclaration declaration = new LocalVariableDeclaration(
		modifiers, typeRef, varSpec);

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
	final FieldReference reference = new FieldReference(field,
		new ParenthesizedExpression(expression));

	return reference;
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
     *            the <code>block</code>'s {@link ExecutionContext}
     * @param block
     *            the {@link StatementBlock} to be put in <code>executionContext</code>
     * @return a new {@link MethodFrame} that associates <code>block</code> with
     *         <code>executionContext</code>
     */
    public static MethodFrame methodFrame(
	    final ExecutionContext executionContext, final StatementBlock block) {
	final MethodFrame frame = KeYJavaASTFactory.methodFrame(null,
		executionContext, block);

	return frame;
    }

    /**
     * Create a method call substitution with a return value assignment.
     * 
     * @param result
     *            the {@link IProgramVariable} <code>block</code>'s return value
     *            is assigned to
     * @param executionContext
     *            the <code>block</code>'s {@link ExecutionContext}
     * @param block
     *            the {@link StatementBlock} to be put in
     *            <code>executionContext</code>
     * @return a new {@link MethodFrame} that associates <code>block</code> with
     *         <code>executionContext</code>
     */
    public static MethodFrame methodFrame(final IProgramVariable result,
	    final ExecutionContext executionContext, final StatementBlock block) {
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
     *            the <code>block</code>'s {@link ExecutionContext}
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
	    final ExecutionContext executionContext,
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
    public static Statement labeledStatement(final Label label,
	    final Statement statement) {
	final LabeledStatement labeled = new LabeledStatement(label, statement);

	return labeled;
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
     * Create a literal for the truth value <code>true</code>.
     * 
     * @return a {@link BooleanLiteral} that represents the value
     *         <code>true</code>
     */
    public static BooleanLiteral trueLiteral() {
	return BooleanLiteral.TRUE;
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
}
