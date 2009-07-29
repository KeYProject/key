// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package paycard;


import javax.swing.*;
import java.awt.*;
import java.awt.event.*;

public class Start {
    public static void main(String[] argv) {
      IssueCardUI gui = new IssueCardUI ();
      gui.initGUI();
    }
}

