// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.rule.metaconstruct;

import java.io.IOException;

import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.*;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.reference.*;
import de.uka.ilkd.key.java.visitor.Visitor;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.ProgramElementName;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.SchemaVariable;
import de.uka.ilkd.key.rule.inst.SVInstantiations;

/** 
 * ProgramTransformers are used to describe schematic transformations 
 * that cannot be expressed by the taclet language itself. For
 * example:
 * <ol>  
 * <li> transformations needing access to the java (type) model, e.g
 * dynamic dispatch of program methods </li>
 * <li> complex transformations that are hard (or not) to express via
 * taclets, for example unwinding a loop (together with replacing
 * continues or unlabeled breaks with a labeled break)</li>
 * </ol>
 * (Program)MetaConstructs should be used with care as they make it hard to
 * validate (verify) rules and import nearly the complete power of Java into
 * taclets.
 */
public abstract class ProgramTransformer extends JavaNonTerminalProgramElement
    implements StatementContainer, Statement, Expression, TypeReference {

    /** the name of the meta construct */
    private Name name;
    /** the encapsulated program element */
    private ProgramElement body;

    /** creates a ProgramTransformer 
     * @param name the Name of the meta construct 
     * @param body the ProgramElement contained by the meta construct 
     */
    public ProgramTransformer(Name name, ProgramElement body) {
	this.name = name;
	this.body = body;
    }

    /** creates a ProgramTransformer 
     * @param name the String with the name of the meta construct
     * @param body the ProgramElement contained by the meta construct 
     */
    public ProgramTransformer(String name, ProgramElement body) {
	this(new Name(name), body);
    }

    /** performs the program transformation needed for symbolic
     * program transformation 
     * @param pe the ProgramElement on which the execution is performed
     * @param services the Services with all necessary information 
     * about the java programs
     * @param svInst the instantiations of the schemavariables 
     * @return the transformated program
     */
    public abstract ProgramElement transform
	(ProgramElement pe, Services services, SVInstantiations svInst);
    
    /** returns the name of the meta construct 
     * @return the name of the meta construct 
     */
    public Name name() {
	return name;
    }

    /** returns the body of the meta construct 
     * @return the body of the meta construct 
     */
    public ProgramElement body() {
	return body;
    }

    /**
     * Finds the source element that occurs last in the source.
     * @return the last source element in the syntactical representation of
     * this element, may be equals to this element.
    */
    public SourceElement getLastElement() {
        return (body != null) ? body : this;
    }

    /**
     * Get the number of statements in this container.
     * @return the number of statements.
     */
    public int getStatementCount() {
	return (body instanceof Statement ? 1 : 0);
    }


    /*
     * Return the statement at the specified index in this node's
     * "virtual" statement array.
     * @param index an index for a statement.
     * @return the statement with the given index.
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     * of bounds.
     */
    public Statement getStatementAt(int index) {
	if (index == 0 && body instanceof Statement) {
	    return (Statement)body;
	} else if (!(body instanceof Statement)) {
	    return null;
	} else {
	    throw new ArrayIndexOutOfBoundsException
		("A ProgramTransformer contains only one statement ");
	}
    }

    /**
     * Returns the number of children of this node.
     * @return an int giving the number of children of this node
     */
    public int getChildCount() {
	return 1;
    }

    /**
     * Returns the child at the specified index in this node's "virtual"
     * child array.
     * @param index an index into this node's "virtual" child array
     * @return the program element at the given position
     * @exception ArrayIndexOutOfBoundsException if <tt>index</tt> is out
     * of bounds
     */
    public ProgramElement getChildAt(int index) {
	return body;
    }
    

    //-------------some methods to pretend being a type reference --------


    public ReferencePrefix getReferencePrefix() {
	return null;
    }

    public ReferencePrefix setReferencePrefix(ReferencePrefix r) {
	return this;
    }


    public int getDimensions() {
	return 0;
    }


    public int getTypeReferenceCount(){
	return 0;
    }

    public TypeReference getTypeReferenceAt(int index) {
	return this;
    }

    public PackageReference getPackageReference() {
	return null;
    }

    public int getExpressionCount() {
	return 0;
    }

    public Expression getExpressionAt(int index) {
	return null;
    }


    public ProgramElementName getProgramElementName() {
	return new ProgramElementName(toString());
    }    

    public String getName() {
	return toString();
    }

    /** calls the corresponding method of a visitor in order to
     * perform some action/transformation on this element
     * @param v the Visitor
     */
    public void visit(Visitor v) {
	v.performActionOnProgramMetaConstruct(this);
    }

    public void prettyPrint(PrettyPrinter p) throws IOException {
        p.printProgramMetaConstruct(this);
    }

    /** to String */
    public String toString() {
	return name+"( "+body+ ");";
    }

    public KeYJavaType getKeYJavaType() {
	return null;
    }

    public KeYJavaType getKeYJavaType(TermServices javaServ) {
	return getKeYJavaType();
    }

    public KeYJavaType getKeYJavaType(Services javaServ, ExecutionContext ec) {
	return getKeYJavaType();
    }
    
    /**
     * get a list of schema variables that are needed by this entity when
     * working given a SV instantiation set.
     * 
     * @param svInst
     *            the instantiations of SV so far.
     * @return a list of schema variables relevant for this entity;
     */
    public ImmutableList<SchemaVariable> needs() {
	return ImmutableSLList.<SchemaVariable>nil();
    }
    
    /**
     * get a list of schema variables that are needed by this entity when
     * working given a SV instantiation set.
     * 
     * @param svInst
     *            the instatiations of SV so far.
     * @return a list of schema variables relevant for this entity;
     */
    public ImmutableList<SchemaVariable> neededInstantiations(SVInstantiations svInst) {
	return ImmutableSLList.<SchemaVariable>nil();
    }

}
