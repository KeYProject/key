/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.speclang;

import java.util.function.UnaryOperator;

import org.key_project.logic.Term;
import org.key_project.rusty.Services;

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
     * Applies a unary operator to every term in this specification element.
     *
     * @param op the operator to apply.
     * @param services services.
     * @return this specification element with the operator applied.
     */
    SpecificationElement map(UnaryOperator<Term> op, Services services);
}
