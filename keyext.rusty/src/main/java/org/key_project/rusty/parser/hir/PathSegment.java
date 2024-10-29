package org.key_project.rusty.parser.hir;

public record PathSegment(Ident ident, HirId hirId, Res res, GenericArgs args, boolean inferArgs) {
}
