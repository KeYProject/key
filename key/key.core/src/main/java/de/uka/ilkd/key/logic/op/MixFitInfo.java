/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.logic.op;

import javax.annotation.Nonnull;

/**
 * @author Alexander Weigl
 * @version 1 (06.02.22)
 */
public class MixFitInfo {
    @Nonnull
    public final Kind kind;
    @Nonnull
    public final String symbol;

    public MixFitInfo(@Nonnull Kind kind, @Nonnull String symbol) {
        this.kind = kind;
        this.symbol = symbol;
    }

    public enum Kind {
        PREFIX, INFIX, SHORTCUT, POSTFIX
    }

    @Nonnull
    public Kind getKind() {
        return kind;
    }

    @Nonnull
    public String getSymbol() {
        return symbol;
    }
}
