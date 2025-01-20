/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.stmt;

import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.Span;

public record Stmt(HirId hirId,StmtKind kind,Span span){}
