/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package org.key_project.rusty.parser.hir.item;

import java.util.Arrays;

import org.key_project.rusty.parser.hir.hirty.HirTy;

//spotless:off
public record FnDecl(HirTy[] inputs, FnRetTy output, boolean cVariadic, ImplicitSelfKind implicitSelf,
                     boolean lifetimeElisionAllowed) {
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
//spotless:on