package org.key_project.rusty.parser.hir.item;

import org.key_project.rusty.parser.hir.hirty.HirTy;

import java.util.Arrays;

public record FnDecl(HirTy[] inputs, FnRetTy output, boolean cVariadic, ImplicitSelfKind implicitSelf, boolean lifetimeElisionAllowed) {
    @Override
    public String toString() {
        return "FnDecl{" +
                "inputs=" + Arrays.toString(inputs) +
                ", output=" + output +
                ", cVariadic=" + cVariadic +
                ", implicitSelf=" + implicitSelf +
                ", lifetimeElisionAllowed=" + lifetimeElisionAllowed +
                '}';
    }
}
