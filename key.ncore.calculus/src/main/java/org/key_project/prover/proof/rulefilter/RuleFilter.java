/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.prover.proof.rulefilter;

import org.key_project.prover.rules.Rule;

/// Interface for objects that represent sets of rules, and which can be used to distinguish
/// different kinds of rules.
public interface RuleFilter {

    boolean filter(Rule rule);

}
