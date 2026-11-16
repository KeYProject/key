/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.ast.declaration.ModifierKind;
import de.uka.ilkd.key.java.ast.statement.MergePointStatement;
import de.uka.ilkd.key.logic.JTerm;
import de.uka.ilkd.key.rule.merge.MergeProcedure;

import org.jspecify.annotations.NullMarked;
import org.jspecify.annotations.Nullable;

/**
 * Specification of a {@link MergePointStatement}.
 *
 * @author Dominic Scheurer
 */
@NullMarked
public interface MergeContract extends SpecificationElement {

    @Override
    MergeContract map(UnaryOperator<JTerm> op, Services services);

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
    default @Nullable ModifierKind getVisibility() {
        assert false : "Method getVisibility() is unimplemented for MergeContract";
        return null;
    }
}
