package org.key_project.rusty.parser.hir.item;

public record Fn(FnSig sig, Generics generics, Body body)implements ItemKind {
}
