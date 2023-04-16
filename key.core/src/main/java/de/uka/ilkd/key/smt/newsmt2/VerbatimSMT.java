/*
 * KEY
 */

/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.uka.ilkd.key.smt.newsmt2;

/**
 * Objects of this class are writable (like {@link SExpr}s), but are not really structured as such.
 * They are just arbitrary strings.
 *
 * Writing them is obvious.
 */
class VerbatimSMT implements Writable {

    private final String string;

    public VerbatimSMT(String string) {
        this.string = string;
    }

    @Override
    public void appendTo(StringBuilder sb) {
        sb.append(string);
    }
}
