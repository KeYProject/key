package org.key_project.rusty.parser.hir.stmt;

import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.Span;

public record Stmt(HirId hirId, StmtKind kind, Span span) {
}
