// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
//
package de.uka.ilkd.key.gui.nodeviews;

import de.uka.ilkd.key.gui.MainWindow;

/**
 * Use this class in case no proof is loaded.
 *
 * @author Kai Wallisch
 */
public class EmptySequent extends SequentView {

    private static final long serialVersionUID = 7572244482555772604L;

    public EmptySequent(MainWindow mainWindow) {
        super(mainWindow);
        setBackground(INACTIVE_BACKGROUND_COLOR);
    }

    @Override
    public String getTitle() {
        return "No proof loaded";
    }

    @Override
    public void printSequent() {
    }

}
