// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.gui;

import java.util.HashMap;

import javax.swing.JRadioButton;

public class JRadioButtonHashMap extends JRadioButton {
    JRadioButtonHashMap(String text, String command, boolean selected, 
            boolean enabled) {
        super(text, selected);
        this.setEnabled(enabled);        
        this.setActionCommand(command);        
        hashmap.put(command, this);        
    }
        
    static HashMap hashmap = new HashMap();
       
    public static JRadioButton getButton(String command) {
        return (JRadioButton) hashmap.get(command);       
    }
}
