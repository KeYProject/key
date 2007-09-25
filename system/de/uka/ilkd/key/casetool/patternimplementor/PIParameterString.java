// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor;

public class PIParameterString extends PIParameter {

    private String value;

    public PIParameterString(String internalName, String name, String value) {
        super(internalName, name);
        setValue(value);
    }

    protected PIParameterString(String internalName, String name) {
        super(internalName, name);
    }

    public String getValue() {
        return value;
    }

    public void setValue(String value) {
        this.value = value;

        //System.out.println("String -
        // setValue(String)\t"+getInternalName()+"\t"+value);
        setChanged();
        notifyObservers(this);
    }
}
