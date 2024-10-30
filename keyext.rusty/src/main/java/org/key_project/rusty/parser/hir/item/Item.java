/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.item;

import org.key_project.rusty.parser.hir.Ident;
import org.key_project.rusty.parser.hir.OwnerId;
import org.key_project.rusty.parser.hir.Span;

public record Item(Ident ident, OwnerId ownerId, ItemKind kind, Span span, Span visSpan) {
}
