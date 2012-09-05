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

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.literal.IntLiteral;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
import de.uka.ilkd.key.java.expression.operator.LessThan;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.java.reference.FieldReference;
import de.uka.ilkd.key.java.reference.ReferencePrefix;
import de.uka.ilkd.key.java.reference.TypeRef;
import de.uka.ilkd.key.java.reference.TypeReference;
import de.uka.ilkd.key.java.statement.*;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.logic.op.ProgramVariable;


/**
 * The KeYASTFactory helps building KeY Java AST structures.
 */
public abstract class KeYJavaASTFactory {

    /** 
     * creates an assignment <code> lhs:=rhs </code>
     */
    public static Statement assign(Expression lhs, Expression rhs) {
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
     *            the named and typed {@link ProgramVariable} to be declared
     * @param init
     *            the {@link Expression} <code>var</code> is initialized with
     * @param type
     *            the static {@link KeYJavaType} of <code>var</code>
     * @return a {@link LocalVariableDeclaration} of <code>var</code> with
     *         static type <code>type</code> and initial value <code>init</code>
     */
    public static LocalVariableDeclaration declare
	(ProgramVariable var, Expression init, KeYJavaType type) {
	return new LocalVariableDeclaration
	    (new TypeRef(type), 
	     new VariableSpecification(var, init, type));
    }

    /**
     * Create a local variable declaration without initialization.
     * 
     * <pre>
     * type var;
     * </pre>
     * 
     * @param var
     *            the named and typed {@link ProgramVariable} to be declared
     * @param type
     *            the static {@link KeYJavaType} of <code>var</code>
     * @return a {@link LocalVariableDeclaration} of <code>var</code> with
     *         static type <code>type</code>
     */
    public static LocalVariableDeclaration declare
	(ProgramVariable var, KeYJavaType type) {
	return new LocalVariableDeclaration
	    (new TypeRef(type), 
	     new VariableSpecification(var, type));
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
     *            the named and typed {@link ProgramVariable} to be declared as
     *            parameter
     * @return a {@link ParameterDeclaration} of <code>var</code> with static
     *         type <code>kjt</code>
     */
    public static ParameterDeclaration parameterDeclaration(JavaInfo javaInfo,
							    KeYJavaType kjt, 
							    ProgramVariable var) {
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

    /**
     * Create an empty statement.
     * 
     * @return a new {@link EmptyStatement}
     */
    public static EmptyStatement emptyStatement() {
	return new EmptyStatement();
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
     * Create a local variable declaration that assigns zero initially.
     * 
     * <pre>
     * type variable = 0;
     * </pre>
     * 
     * @param type
     *            the static {@link KeYJavaType} of <code>variable</code>
     * @param variable
     *            the named and typed {@link ProgramVariable} to be declared
     * @return a new {@link LocalVariableDeclaration} of <code>variable</code>
     *         with static type <code>type</code> and initial value zero
     */
    public static LocalVariableDeclaration declareZero(final KeYJavaType type,
	    final ProgramVariable variable) {
	return KeYJavaASTFactory.declare(variable, new IntLiteral(0), type);
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
     *            the named and typed {@link ProgramVariable} to be declared
     * @return a new {@link ILoopInit} that declares variable
     *         <code>variable</code> with static type <code>type</code> and
     *         initial value zero
     */
    public static ILoopInit loopInit(final KeYJavaType type,
	    final ProgramVariable variable) {
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
}
