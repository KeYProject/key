/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2, 
 * or (at your option) any later version.
 * SPDX-License-Identifier: GPL-2.0-or-later */
package org.key_project.prover.indexing;

/// Enum encoding which rule application index to use:
/// The interactive ones contains also rules without rulesets. These are usually not applied
/// by strategies, and hence, waste matching lookup and effort when used in automated proof search.
///
/// Nevertheless, some strategies/macros, use rules without rulesets and require the interactive
/// index.
public enum RuleAppIndexMode {
    AUTO, INTERACTIVE
}
