package org.key_project.rusty.parser.hir;

public record Span(int lo, int hi, LocalDefId parent) {
}
