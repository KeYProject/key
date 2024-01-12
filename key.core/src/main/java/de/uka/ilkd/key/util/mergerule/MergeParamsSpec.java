/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.util.mergerule;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.LocationVariable;
import de.uka.ilkd.key.speclang.MergeContract;

import org.key_project.util.collection.ImmutableList;

/**
 * Specification of merge parameters for the creation of {@link MergeContract}s;
 *
 * @author Dominic Scheurer
 */
public record MergeParamsSpec(String latticeType, LocationVariable placeholder, ImmutableList<Term> predicates) {
}
