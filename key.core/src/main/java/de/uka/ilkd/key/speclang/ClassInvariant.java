/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermServices;
import de.uka.ilkd.key.logic.op.ParsableVariable;
import de.uka.ilkd.key.speclang.Contract.OriginalVariables;


/**
 * A class invariant. Objects of type ClassInvariant are an intermediate result of the specification
 * language front ends; ultimately, they give rise to instances of the ClassAxiom class (more
 * precisely, of its subclasses RepresentsAxiom and PartialInvAxiom), through which class invariants
 * are actually used in proofs.
 */
public interface ClassInvariant extends SpecificationElement {


    /**
     * Returns the invariant formula without implicit all-quantification over the receiver object.
     */
    Term getInv(ParsableVariable selfVar, TermServices services);


    /**
     * Returns the invariant formula without implicit all-quantification over the receiver object.
     */
    Term getOriginalInv();


    /**
     * Tells whether the invariant is static (i.e., does not refer to a receiver object).
     */
    boolean isStatic();

    /**
     * Tells whether the invariant is free (i.e., can be assumed without proof).
     */
    boolean isFree();

    /**
     * Returns another class invariant like this one, except that it refers to the passed
     * KeYJavaType.
     */
    ClassInvariant setKJT(KeYJavaType kjt);

    /**
     * Returns the original Self Variable to replace it easier.
     */
    OriginalVariables getOrigVars();

    @Override
    ClassInvariant map(UnaryOperator<Term> op, Services services);

}
