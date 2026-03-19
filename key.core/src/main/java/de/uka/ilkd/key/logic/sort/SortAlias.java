/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.logic.sort;

import org.key_project.logic.Name;
import org.key_project.logic.Named;
import org.key_project.logic.sort.Sort;

/// An alias for a sort, allowing for more ergonomic usage of parametric sorts. E.g., `LocSet` may
/// be defined in the future as `\alias LocSet = Set<[Tuple2<[Object, Field]>]>`.
/// These aliases are managed by the Services, where sort lookup takes them into account and
/// directly resolves to the aliased sort.
/// Hence, aliases are syntactic sugar in KeY files and are not directly part of the logic.
public record SortAlias(Name name, Sort aliasedSort) implements Named {
}
