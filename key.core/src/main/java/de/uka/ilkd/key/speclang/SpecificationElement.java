/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;
import javax.annotation.Nullable;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.modifier.VisibilityModifier;
import de.uka.ilkd.key.logic.Term;


/**
 * Common superinterface of all constructs created by the specification language front ends and
 * managed by SpecificationRepository.
 */
public interface SpecificationElement {

    /**
     * Returns the unique internal name of the specification element.
     */
    String getName();

    /**
     * Returns the displayed name.
     */
    String getDisplayName();

    /**
     * Returns the visibility of the invariant (null for default visibility)
     */
    @Nullable
    VisibilityModifier getVisibility();


    /**
     * Returns the KeYJavaType representing the class/interface to which the specification element
     * belongs.
     */
    KeYJavaType getKJT();

    /**
     * Applies a unary operator to every term in this specification element.
     *
     * @param op the operator to apply.
     * @param services services.
     * @return this specification element with the operator applied.
     */
    SpecificationElement map(UnaryOperator<Term> op, Services services);
}
