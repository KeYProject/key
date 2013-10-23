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

import de.uka.ilkd.key.logic.label.TermLabelManager;
import de.uka.ilkd.key.logic.label.TermLabelUtil;
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
 * via {@link LabelFactory#getLabel(String, java.util.List)}.
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
 * Please see information in {@link TermLabelUtil} on how to introduce new label types.
 * </p>
 * 
 * @see TermLabelInstantiator
 * @see TermLabelManager
 * @see TermLabelUtil
 * 
 * @author Martin Hentschel
 */
public interface TermLabel extends Named {
    
    /**
     * Retrieves the i-th parameter object of this term label.
     * 
     * <p>
     * A term label may have structure, i.e. can be parameterized.
     * 
     * @param i
     *            the number of the parameter to retrieve (
     *            {@code 0 <= i < getChildCount()})
     * @return the selected parameter
     * @throw an {@link IndexOutOfBoundsException} if the given parameter number
     *        <tt>i</tt> is negative or greater-or-equal the number of
     *        parameters returned by {@link #getChildCount()}
     */
    public Object getChild(int i);

    /**
     * Gets the number of parameters of this term label.
     *  
     * @return the number of parameters (a non-negative number)
     */
    public int getChildCount();
    
    /**
     * Gets the instantiator associated to this label.
     * 
     * <p>
     * Every term label <i>can</i> have a {@link TermLabelInstantiator}
     * associated with it. If it does not, this method returns
     * <code>null</code>.
     * 
     * @return the associated instantiator or <code>null</code>
     */
    public TermLabelInstantiator getInstantiator();
}