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

import java.util.ArrayList;

public class PIParameters {

    ArrayList parameters;

    public PIParameters() {
        parameters = new ArrayList();
    }

    public void remove(int i) {
        parameters.remove(i);
    }

    public void set(int i, PIParameter pip) {
        parameters.set(i, pip);
    }

    public int size() {
        return parameters.size();
    }

    public void add(PIParameter pip) {
        parameters.add(pip);
    }

    public PIParameter get(int i) {
        return (PIParameter) parameters.get(i);
    }

    public PIParameter get(String internalName) {
        for (int i = 0; i < size(); i++) {
            //System.out.println("Comparing " +internalName + " with " +
            // get(i).getInternalName());
            if (get(i).getInternalName().equals(internalName)) {
                //System.out.println("match!! "+internalName);
                return get(i);
            } else if (get(i) instanceof PIParameterGroup) {
                //System.out.println(get(i)+" is PIParameterGroup
                // "+internalName);
                PIParameter tmp = ((PIParameterGroup) get(i)).get(internalName);

                if (tmp == null) {
                    //System.out.println("group - no match!! " + internalName);
                    continue;
                } else if (tmp.getInternalName().equals(internalName)) {
                    //System.out.println("group - match!! " +internalName);
                    return tmp;
                }
            }
        }

        //System.out.println("couldn't find " + internalName);
        return null;
    }

    public void clear() {
        parameters.clear();
    }

    public String toString() {
        String retval = new String();
        retval = "{\n";

        for (int i = 0; i < size(); i++) {
            retval = retval + /* get(i).getClass() +"\t"+ */
            get(i).getInternalName() + get(i).getName() + "\n";

            if (get(i) instanceof PIParameterGroup) {
                retval = retval + get(i).toString();
            }
        }

        return retval + "}";
    }
}
