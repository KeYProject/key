// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.declaration.Modifier;
import de.uka.ilkd.key.java.declaration.ParameterDeclaration;
import de.uka.ilkd.key.java.declaration.VariableSpecification;
import de.uka.ilkd.key.java.expression.operator.CopyAssignment;
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


    public static LocalVariableDeclaration declare
	(ProgramVariable var, Expression init, KeYJavaType type) {
	return new LocalVariableDeclaration
	    (new TypeRef(type), 
	     new VariableSpecification(var, init, type));
    }

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

    public static Catch catchClause(JavaInfo javaInfo, String param, 
				    KeYJavaType kjt, StatementBlock body) {

	return new Catch(parameterDeclaration(javaInfo, kjt, param), body);
    }

    public static Catch catchClause(JavaInfo javaInfo, String param, 
				    String type, StatementBlock body) {

	return catchClause(javaInfo, param, 
			   javaInfo.getKeYJavaType(type), body);
    }
    

    public static Throw throwClause(Expression e) {
	return new Throw(e);
    }

    public static Return returnClause(Expression e) {
	return new Return(e);
    }


    public static If ifThen(Expression guard, 
			    Statement then) {
	return new If(guard, new Then(then));
    }

    public static If ifElse(Expression guard, 
		     Then then,
		     Else els) {
	return new If(guard, then, els);
    }

    public static Break breakStatement(Label l) {
	return new Break(l);
    }

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
	return new StatementBlock(new ArrayOfStatement(block));	
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

}
