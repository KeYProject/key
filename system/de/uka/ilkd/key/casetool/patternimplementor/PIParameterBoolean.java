// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.casetool.patternimplementor;

public class PIParameterBoolean extends PIParameter {

    private Boolean value;

    public PIParameterBoolean(String internalName, String name, boolean value) {
        super(internalName, name);
        setValue(value);
    }

    public PIParameterBoolean(String internalName, String name, Boolean value) {
        super(internalName, name);
        setValue(value);
    }

    public PIParameterBoolean(String internalName, String name, String value) {
        super(internalName, name);
        setValue(value);
    }

    public String getValue() {
        return value.toString();
    }

    public void setValue(Boolean value) {
        this.value = value;

        //System.out.println("Boolean -
        // setValue(Boolean)\t"+getInternalName()+"\t"+getValue());
        setChanged();
        notifyObservers(this);
    }

    public void setValue(boolean value) {
        setValue(new Boolean(value));
    }

    public void setValue(String value) {
        //System.out.println("setting boolean value to "+value);
        setValue(value.equals("true"));
    }
}
