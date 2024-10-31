/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.item;

import org.key_project.rusty.parser.hir.Path;
import org.key_project.rusty.parser.hir.Res;
import org.key_project.util.collection.ImmutableArray;

public record Use(Path<ImmutableArray<Res>> path, UseKind kind) implements ItemKind {
    public enum UseKind {
        Single, Glob, ListStem
    }
}
