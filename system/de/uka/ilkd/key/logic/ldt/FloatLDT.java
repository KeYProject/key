// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.

package de.uka.ilkd.key.logic.ldt;

import de.uka.ilkd.key.java.Expression;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.PrimitiveType;
import de.uka.ilkd.key.java.expression.Literal;
import de.uka.ilkd.key.java.reference.ExecutionContext;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Namespace;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.util.ExtList;

/**
 * Complete this class if you want to add support for the Java double type.
 * 
 * At the moment this class contains only stubs.
 */
public class FloatLDT extends LDT {

    public FloatLDT(Namespace sorts, Namespace functions) {
	super(new Name("jfloat"), sorts, PrimitiveType.JAVA_FLOAT);
    }

    /**
     * returns true if the LDT is responsible for this kind of literals
     * 
     * @param lit
     *            the Literal
     * @return true if the LDT is responsible for this kind of literals
     */
    public boolean isResponsible(Literal lit) {
	return false;
    }

    /**
     * returns true if the LDT offers an operation for the given java operator
     * and the logic subterms
     * 
     * @param op
     *            the de.uka.ilkd.key.java.expression.Operator to translate
     * @param subs
     *            the logic subterms of the java operator
     * @return true if the LDT offers an operation for the given java operator
     *         and the subterms
     */
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    Term[] subs, Services services, ExecutionContext ec) {
	return false;
    }

    /**
     * returns true if the LDT offers an operation for the given binary java
     * operator and the logic subterms
     * 
     * @param op
     *            the de.uka.ilkd.key.java.expression.Operator to translate
     * @param left
     *            the left subterm of the java operator
     * @param right
     *            the right subterm of the java operator
     * @return true if the LDT offers an operation for the given java operator
     *         and the subterms
     */
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    Term left, Term right, Services services, ExecutionContext ec) {
	return false;

    }

    /**
     * returns true if the LDT offers an operation for the given unary java
     * operator and the logic subterms
     * 
     * @param op
     *            the de.uka.ilkd.key.java.expression.Operator to translate
     * @param sub
     *            the logic subterms of the java operator
     * @return true if the LDT offers an operation for the given java operator
     *         and the subterm
     */
    public boolean isResponsible(de.uka.ilkd.key.java.expression.Operator op,
	    Term sub, Services services, ExecutionContext ec) {
	return false;
    }

    /**
     * translates a given literal to its logic counterpart
     * 
     * @param lit
     *            the Literal to be translated
     * @return the Term that represents the given literal in its logic form
     */
    public Term translateLiteral(Literal lit) {
	return null;
    }

    /**
     * returns the function symbol for the given operation
     * 
     * @return the function symbol for the given operation
     */
    public Function getFunctionFor(de.uka.ilkd.key.java.expression.Operator op,
	    Services services, ExecutionContext ec) {
	return null;
    }

    public boolean hasLiteralFunction(Function f) {
	return false;
    }

    public Expression translateTerm(Term t, ExtList children) {
	throw new RuntimeException(
		"FloatLDT: We do not yet support double or floats on the master branch of KeY");
    }
}
