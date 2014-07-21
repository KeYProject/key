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

//// This file is part of KeY - Integrated Deductive Software Design
//// Copyright (C) 2001-2011 Universitaet Karlsruhe, Germany
////                         Universitaet Koblenz-Landau, Germany
////                         Chalmers University of Technology, Sweden
////
//// The KeY system is protected by the GNU General Public License. 
//// See LICENSE.TXT for details.
////
////
//
//package de.uka.ilkd.key.gui;
//
//import java.util.HashMap;
//
//import javax.swing.JRadioButton;
//
//public class JRadioButtonHashMap extends JRadioButton {
//    /**
//     * 
//     */
//    private static final long serialVersionUID = 785796009937827348L;
//
//    JRadioButtonHashMap(String text, String command, boolean selected, 
//            boolean enabled) {
//        super(text, selected);
//        this.setEnabled(enabled);        
//        this.setActionCommand(command);        
//        hashmap.put(command, this);        
//    }
//        
//    static HashMap<String, JRadioButtonHashMap> hashmap = new HashMap<String, JRadioButtonHashMap>();
//       
//    public static JRadioButton getButton(String command) {
//        return hashmap.get(command);       
//    }
//}