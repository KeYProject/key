package org.key_project.rusty.parser.hir.pat;

import org.key_project.rusty.parser.hir.HirId;
import org.key_project.rusty.parser.hir.Span;

public record Pat(HirId hirId, PatKind kind, Span span, boolean defaultBindingModes) {
}
