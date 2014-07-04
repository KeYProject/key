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

package de.uka.ilkd.key.util;

import java.util.Random;

public final class TipOfTheDay {

    private final static Random r = new Random();
    private final static String[] TIPS = new String[] {
        "Press CTRL+F to search in sequents.",
        "Proofs can be quick-saved by pressing F5.",
	"Use the command line option '--experimental' to activate experimental features.",
	"Pressing ALT when moving the cursor over a term shows some more information.",
        "Some rules are not available to the user when One-Step-Simplification is turned on.",
        "You can search for node numbers or rule names in the proof tree view (press CTRL+SHIFT+F).",
        "Install an SMT solver to help KeY solve problems; CVC3, Simplify, Yices, and Z3 are supported.",
        "In the right-click menu you can abbreviate terms."
    };


    public static String get() {
        return TIPS[r.nextInt(TIPS.length)];
    }


}