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

import java.awt.event.ActionListener;
import java.util.Observable;
import java.util.Observer;

import javax.swing.JComponent;
import javax.swing.JPanel;

public abstract class PIParameterGUI extends JPanel implements Observer, ActionListener {

    protected JComponent content;

    protected PIParameter pip;

    public PIParameterGUI(PIParameter pip) {
        super();
        this.pip = pip;
        pip.addObserver(this);
        buildGUI();
    }

    public void update(Observable o, Object arg) {
        //System.out.println("update\t" + o + "\t" + arg);

        updateGUI();
    }

    protected abstract void buildGUI();

    protected void updateGUI() {
        //System.out.println("GUI.updateGUI "+pip.getName());
    }
}
