package org.key_project.rusty.speclang.spec;

import org.jspecify.annotations.Nullable;
import org.key_project.rusty.parser.hir.DefId;

public record SpecCase(DefId did, SpecKind kind, String name, Term[] pre, Term[] post, @Nullable Term variant, Term diverges) {
}
