/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.proof.init;



public interface Profile {
    /** returns the rule source containg all taclets for this profile */
    RuleCollection getStandardRules();

    /** the name of this profile */
    String name();
}
