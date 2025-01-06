/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;


public interface Rule
        extends org.key_project.prover.rules.Rule {
    /**
     * returns the display name of the rule
     */
    String displayName();
}
