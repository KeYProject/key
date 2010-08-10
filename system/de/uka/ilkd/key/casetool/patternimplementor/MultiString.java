// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor;

import java.util.ArrayList;
import java.util.StringTokenizer;

public class MultiString {

    ArrayList strings;

    public MultiString() {
        strings = new ArrayList();
    }

    /**
     * this should parse the 'string' into several strings uses white-spaces,
     * comma "," and semicolon ";" as delimiter. eg: input: "as, afsiop, poa,
     * asfs fmio, apom ;aspo" should be parsed to output:["as", "afsiop", "poa",
     * "asfs", "fmio", "apom", "aspo"]
     */
    public static MultiString parse(String string) {
        MultiString ms = new MultiString();
        StringTokenizer st = new StringTokenizer(string, " \t\n\r\f,;");

        while (st.hasMoreTokens()) {
            String tmp = st.nextToken();

            if (tmp.length() > 0) {
                ms.add(tmp);
            }
        }

        return ms;
    }

    public String toString() {
        if (size() <= 0) { return new String(); }

        String retval = new String(get(0));

        for (int i = 1; i < size(); i++) {
            retval = retval + ", " + get(i);
        }

        return retval;
    }

    public int size() {
        return strings.size();
    }

    public void add(String string) {
        strings.add(string);
    }

    public String get(int i) {
        return (String) strings.get(i);
    }

    public void clear() {
        strings.clear();
    }
}
