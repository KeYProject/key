/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.speclang;

import java.util.function.UnaryOperator;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.Term;

/**
 * A contract about the dependencies of an observer symbol, consisting of a precondition, a depends
 * clause, and a measured-by clause.
 */
public interface DependencyContract extends Contract {

    @Override
    public DependencyContract map(UnaryOperator<Term> op, Services services);
}
