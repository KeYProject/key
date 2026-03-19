/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.sort.Sort;

public record SortAlias(Name name, Sort aliasedSort) implements Named {
}
