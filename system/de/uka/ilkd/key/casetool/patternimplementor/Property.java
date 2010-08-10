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

import java.util.Vector;

public class Property {

    /*
     *  - name <- String - value <- vector of Strings
     */
    private String name;

    private Vector value;

    public Property(String name, Vector value) {
        for (int i = 0; i < value.size(); i++) {
            if (!(value.elementAt(i) instanceof String)) {
                System.err.println("Error in Property.Property");

                return;
            }
        }

        this.value = value;
        this.name = name;
    }

    public String toString() {
        return name + " = " + value;
    }

    public int size() {
        return value.size();
    }

    public String getName() {
        return name;
    }

    public String getValue(int i) {
        if ((i >= 0) && (i < value.size())) { return (String) value
                .elementAt(i); }

        return null;
    }

    public String getValue() {
        return (String) value.elementAt(0);
    }
}
