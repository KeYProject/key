// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2017 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.speclang;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.rule.merge.MergeProcedure;

/**
 * Specification of a {@link MergePointStatement}.
 *
 * @author Dominic Scheurer
 */
public interface MergeContract extends SpecificationElement {
    
    /**
     * @return The {@link MergePointStatement} specified by this {@link MergeContract}.
     */
    MergePointStatement getMergePointStatement();
    
    /**
     * @return The {@link MergeProcedure} {@link Class} for the {@link MergePointStatement}.
     */
    Class<? extends MergeProcedure> getMergeProcedure();
    
    /**
     * @param services TODO
     * @return The instantiated {@link MergeProcedure}.
     */
    MergeProcedure getInstantiatedMergeProcedure(Services services);
    
    default VisibilityModifier getVisibility() {
        assert false : "Method getVisibility() is unimplemented for MergeContract";
        return null;
    }
}
