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

import java.util.Arrays;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * The interface for term labels. Term labels are annotations that can be attached
 * to {@link Term}s and carry additional information. They must not be soundness relevant.
 */
public interface ITermLabel extends Named {

    /**
     * List of all "relevant" TermLabels. This is used for TermLabelCondition
     * (a VariableCondition). If you want any other TermLabels to be used in
     * TermLabelCondition, please add them here.
     */
    public static final Set<ITermLabel> labels =
            Collections.unmodifiableSet(new LinkedHashSet<ITermLabel>(Arrays.asList(
                    LoopBodyTermLabel.INSTANCE, LoopInvariantNormalBehaviorTermLabel.INSTANCE,
                    ShortcutEvaluationTermLabel.INSTANCE, ImplicitTermLabel.INSTANCE)));

    /**
     * A term label may have structure, i.e., parameterized
     * @param i the i-th parameter (from 0 to max nr of parameters)
     * @return the selected parameter
     * @throw an {@link IndexOutOfBoundsException} if the given parameter
     * number is negative or greater-or-equal the number of parameters
     * returned by {@link #getChildCount()}
     */
    public abstract Object getChild(int i);

    /**
     * number of parameters (non-negative number)
     * @return the number of parameters
     */
    public abstract int getChildCount();
}