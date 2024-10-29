package org.key_project.rusty.parser.hir.hirty;

import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.Span;

public record HirTy(HirId hirId, HirTyKind kind, Span span) {
}
