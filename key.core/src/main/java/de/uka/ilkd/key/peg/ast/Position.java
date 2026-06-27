/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.peg.ast;

import org.jspecify.annotations.NullMarked;

/**
 * Represents the source code position range of an AST node.
 * Contains start and end line/column information.
 *
 * @param startLine Start line number (1-based)
 * @param startColumn Start column number (0-based)
 * @param endLine End line number (1-based)
 * @param endColumn End column number (0-based)
 *
 * @author Cline
 * @version 1.0
 */
@NullMarked
public record Position(int startLine, int startColumn, int endLine, int endColumn) {
}