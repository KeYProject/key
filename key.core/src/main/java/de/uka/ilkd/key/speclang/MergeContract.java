/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.java.statement.MergePointStatement;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.merge.MergeProcedure;

/**
 * Specification of a {@link MergePointStatement}.
 *
 * @author Dominic Scheurer
 */
public interface MergeContract extends SpecificationElement {

    @Override
    MergeContract map(UnaryOperator<Term> op, Services services);

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

    @Override
    default VisibilityModifier getVisibility() {
        assert false : "Method getVisibility() is unimplemented for MergeContract";
        return null;
    }
}
