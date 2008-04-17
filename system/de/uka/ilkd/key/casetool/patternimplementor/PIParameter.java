// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor;

import java.util.Observable;

public abstract class PIParameter extends Observable {

    //	public abstract String getValue();
    //    public abstract void setValue(String value);
    private String name;

    private String internalName;

    /**
     * PIParameter(String internalName, String name)
     */
    public PIParameter(String internalName, String name) {
        setName(name);
        setInternalName(internalName);
    }

    public void setName(String name) {
        this.name = name;
    }

    public String getName() {
        return name;
    }

    public String getInternalName() {
        return internalName;
    }

    public void setInternalName(String internalName) {
        this.internalName = internalName;
    }

    public String getValue() {
        return "<-getValue not defined for this type->";
    }
}
