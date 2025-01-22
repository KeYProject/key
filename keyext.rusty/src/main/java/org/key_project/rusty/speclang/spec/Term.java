package org.key_project.rusty.speclang.spec;

import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.Span;

public record Term(HirId hirId, TermKind kind, Span span) {
}
