/* This file is part of KeY - https://key-project.org
 * KeY is licensed by the GNU General Public License Version 2
 * SPDX-License-Identifier: GPL-2.0 */
package de.uka.ilkd.key.smt.newsmt2;

/**
 * Objects of this class are writable (like {@link SExpr}s), but are not really structured as such.
 * They are just arbitrary strings.
 *
 * Writing them is obvious.
 */
class VerbatimSMT implements Writable {

    private String string;

    public VerbatimSMT(String string) {
        this.string = string;
    }

    @Override
    public void appendTo(StringBuilder sb) {
        sb.append(string);
    }
}
