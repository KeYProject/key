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


public class PIParameterMultiString extends PIParameterString {

    private MultiString value;

    public PIParameterMultiString(String internalName, String name, String value) {
        this(internalName, name, MultiString.parse(value));
    }

    public PIParameterMultiString(String internalName, String name,
            MultiString value) {
        super(internalName, name);
        this.value = value;
    }

    public String getValue() {
        //System.out.println("Trying to get one String from MultiString");
        return value.toString();
    }

    public String[] getValues() {
        String[] values = new String[value.size()];

        for (int i = 0; i < value.size(); i++) {
            values[i] = value.get(i);
        }

        return values;
    }

    public MultiString getMultiString() {
        return value;
    }

    public void setValue(String value) {
        //System.out.println("MultiString.setValue");
        this.value = MultiString.parse(value);

        //System.out.println("MultiString -
        // setValue(String)\t"+getInternalName()+"\t"+this.value);
        setChanged();
        notifyObservers(this);
    }

    public int size() {
        return value.size();
    }
}
