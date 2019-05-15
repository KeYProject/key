/*
 * KEY
 */

/*
 * This file is part of AlgoVer.
 *
 * Copyright (C) 2015-2016 Karlsruhe Institute of Technology
 */
package de.uka.ilkd.key.smt.newsmt2;

public class VerbatimSMT implements Writable {

    private String string;

    public VerbatimSMT(String string) {
        this.string = string;
    }

    @Override
    public void appendTo(StringBuffer sb) {
        sb.append(string);
    }
}
