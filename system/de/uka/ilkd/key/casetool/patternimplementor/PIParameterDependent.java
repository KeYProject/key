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

import java.util.Observable;
import java.util.Observer;

/**
 * This is a PIParameterGroup that is dependent of a PIParameterMultiString The
 * number of elements in the Group are equal to the size of the MultiString
 */
public class PIParameterDependent extends PIParameterGroup implements Observer {

    // multistring to watch
    PIParameterMultiString pipms;

    public PIParameterDependent(String internalName, String name,
            PIParameterMultiString pipms) {
        super(internalName, name); //, new PIParameters());

        pipms.addObserver(this);
        this.pipms = pipms;
        adjustGroup();
    }

    public void update(Observable o, Object arg) {
        //System.out.println("PIPDependent : update");
        adjustGroup();

        //   		setChanged();
        //        notifyObservers(this);
    }

    public void adjustGroup() {
        //System.out.println("Dependent,adjustGroup");
        PIParameters pips = new PIParameters();

        for (int i = 0; i < pipms.size(); i++) {
            if (i < group.size()) {
                group.get(i).setName(pipms.getMultiString().get(i));
                pips.add(group.get(i));

                //System.out.println("old size: "+i);
            } else {
                pips.add(new PIParameterMultiString(getInternalName(), pipms
                        .getMultiString().get(i), getInternalName() + (i + 1)));

                //System.out.println("new size: "+i);
            }
        }

        this.group = pips;
        setChanged();
        notifyObservers(pips);
    }

    public PIParameter get(int i) {
        return group.get(i);
    }

    public PIParameterMultiString getSubject() {
        return pipms;
    }
}
