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

package de.uka.ilkd.key.logic;

import de.uka.ilkd.key.rule.label.TermLabelInstantiator;


/**
 * <p>
 * The interface for term labels. Term labels are annotations that can be attached
 * to {@link Term}s and carry additional information. 
 * <b>They must not be soundness relevant</b>. But they may be used in strategies
 * to compute the order in which rules are applied.
 * </p>
 * <p>
 * A term label can have parameters accessible via {@link #getChild(int)} and
 * {@link #getChildCount()}. Such parameters can be any {@link Object}.
 * But keep in mind that it is required to parse {@link String}s into {@link Term}s,
 * e.g. if it is used in a Taclet definition or if a cut rule is applied.
 * For convenience parameters are always printed as {@link String}s
 * and have to be parsed individually into the required {@link Object} instances
 * via {@link LabelFactory#createLabel(String, java.util.List)}.
 * </p>
 * <p>
 * {@link Term}s with or without term labels are still unmodifiable.
 * It is recommended to implement {@link TermLabel}s also unmodifiable.
 * This means also that it is recommended that parameters of {@link TermLabel}s are also unmodifiable.
 * </p>
 * <p>
 * During proof it is the responsibility of {@link de.uka.ilkd.key.rule.label.TermLabelInstantiator} instances to
 * maintain or remove existing term labels or to add new one.
 * </p>
 * <p>
 * To implement a new term label the following steps are required:
 * <ol>
 *    <li>Create a subclass of {@link TermLabel}.</li>
 *    <li>Modify {@link LabelFactory#createLabel(String, java.util.List)} to ensure that instances of the new {@link TermLabel} sub class are created when a {@link String} is parsed into a {@link Term}.</li>
 *    <li>If required implement an {@link de.uka.ilkd.key.rule.label.TermLabelInstantiator} which maintains the new term labels during proof. Ensure that this {@link de.uka.ilkd.key.rule.label.TermLabelInstantiator} instance is registered in {@link de.uka.ilkd.key.proof.init.Profile#getLabelInstantiators()}.
 *        Typically this is achieved by adding the new {@link de.uka.ilkd.key.rule.label.TermLabelInstantiator} instance in
 *        {@link de.uka.ilkd.key.proof.init.AbstractProfile#computeLabelInstantiators()}.</li>
 * </ol>
 * </p>
 */
public interface TermLabel extends Named {
    /**
     * A term label may have structure, i.e., parameterized
     * @param i the i-th parameter (from 0 to max nr of parameters)
     * @return the selected parameter
     * @throw an {@link IndexOutOfBoundsException} if the given parameter number is negative or greater-or-equal the number of parameters returned by {@link #getChildCount()}
     */
    public Object getChild(int i);

    /**
     * number of parameters (non-negative number)
     * @return the number of parameters
     */
    public int getChildCount();
    
    public TermLabelInstantiator getInstantiator();
}