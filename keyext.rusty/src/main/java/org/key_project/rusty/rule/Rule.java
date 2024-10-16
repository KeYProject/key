/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.rule;

import org.key_project.logic.Named;
import org.key_project.ncore.rules.RuleAbortException;
import org.key_project.rusty.proof.Goal;
import org.key_project.util.collection.ImmutableList;

import org.jspecify.annotations.NonNull;

public interface Rule
        extends org.key_project.ncore.rules.Rule, Named {
    /**
     * returns the display name of the rule
     */
    String displayName();
}
