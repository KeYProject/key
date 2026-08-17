/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.java.ast;

import de.uka.ilkd.key.rule.MatchConditions;

import org.jspecify.annotations.Nullable;

/**
 *
 * @author Alexander Weigl
 * @version 1 (25.04.26)
 */
public interface Matchable {
    @Nullable
    MatchConditions match(Object o, MatchConditions cond);
}
