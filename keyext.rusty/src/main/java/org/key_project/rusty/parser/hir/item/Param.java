package org.key_project.rusty.parser.hir.item;

import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.Span;
import org.key_project.rusty.parser.hir.pat.Pat;

public record Param(HirId hirId, Pat pat, Span tySpan, Span span) {
}
