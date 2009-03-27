// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
package de.uka.ilkd.key.casetool.patternimplementor;


public class PIParameterGroup extends PIParameter {

    protected PIParameters group;

    public PIParameterGroup(String internalName, String name) {
        super(internalName, name);
        this.group = new PIParameters();
    }

    public String getValue(int i) {
        return group.get(i).getValue();
    }

    public String[][] getValues() {
        String[][] values = new String[size()][];

        for (int i = 0; i < size(); i++) {
            String[] tmp = ((PIParameterMultiString) group.get(i)).getValues();
            values[i] = tmp;
        }

        return values;
    }

    public void add(PIParameter pip) {
        group.add(pip);
    }

    public int size() {
        return group.size();
    }

    public PIParameter get(int i) {
        return group.get(i);
    }

    public PIParameter get(String internalName) {
        PIParameter tmp = group.get(internalName);

        //System.out.println(internalName + " getting "+tmp + " from
        // "+getInternalName());
        return tmp;
    }

    public String toString() {
        String retval = new String();

        /*
         * retval = "internalName = "+getInternalName() + "\n"; retval = retval +
         * "name = " + getName() +"\n";
         */
        retval = retval + group;

        return retval;
    }
}
