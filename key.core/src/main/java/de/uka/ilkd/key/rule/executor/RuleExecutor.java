/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule.executor;

import de.uka.ilkd.key.proof.Goal;
import de.uka.ilkd.key.rule.RuleApp;

import org.key_project.util.collection.ImmutableList;


/**
 * Executes a Rule with respect to a given instantiation of the schemavariables.
 */
public interface RuleExecutor extends org.key_project.prover.rules.RuleExecutor<Goal> {

}
