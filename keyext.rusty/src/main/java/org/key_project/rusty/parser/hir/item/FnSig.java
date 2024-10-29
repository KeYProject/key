package org.key_project.rusty.parser.hir.item;

import org.key_project.rusty.parser.hir.Span;

public record FnSig(FnHeader header, FnDecl decl, Span span) {
}
