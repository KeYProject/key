// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.gui.nodeviews;

import java.awt.event.ActionListener;

import de.uka.ilkd.key.rule.TacletApp;

/**
 * This interface is implemented by items to be displayed in 
 * the @link TacletMenu.
 */
interface TacletMenuItem {
    
    
    void addActionListener(ActionListener listener);
    
    /** gets the Taclet that is attached to this item
     * @return the attached Taclet
     */
    abstract TacletApp connectedTo();

}