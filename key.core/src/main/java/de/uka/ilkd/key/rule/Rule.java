/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.rule;


import org.key_project.logic.HasOrigin;


/**
 * This interface has to be implemented by all classes that want to act as a rule in the calculus.
 */
public interface Rule extends org.key_project.prover.rules.Rule, HasOrigin {
}
