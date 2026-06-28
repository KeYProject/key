package org.key_project.key.ast;

/**
 * Represents the source code position range of an AST node.
 * Contains start and end line/column information.
 *
 * @param startLine   Start line number (1-based)
 * @param startColumn Start column number (0-based)
 * @param endLine     End line number (1-based)
 * @param endColumn   End column number (0-based)
 * @author Cline
 * @version 1.0
 */

public record Position(int startLine, int startColumn, int endLine, int endColumn) {
}