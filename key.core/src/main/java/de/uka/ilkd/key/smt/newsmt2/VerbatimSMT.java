/* This file is part of KeY - https://key-project.org
 * KeY is licensed under the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0-only */
package de.uka.ilkd.key.smt.newsmt2;

/**
 * Objects of this class are writable (like {@link SExpr}s), but are not really structured as such.
 * They are just arbitrary strings.
 * <p>
 * Writing them is obvious.
 */
record VerbatimSMT(String string) implements Writable {

    @Override
    public void appendTo(StringBuilder sb) {
        sb.append(string);
    }
}
