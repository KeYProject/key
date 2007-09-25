// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.pp;


import java.io.IOException;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.util.pp.Layouter;


/** Hack! The class {@link LogicPrinter} contains the code for
 * printing formulas and terms, and restricts acccess to the low level
 * methods. But the {@link SeqentPrinter} can only print terms, that
 * it knows. Because of the access limitations, it is not possible to
 * invoke these methodsfrom other packages.
 *
 * This class wraps these methods and make them available public. This
 * class should only be used by the ASM term printer class.
 *
 * @author Hubert Schmid */

public class AbstractAsmPrinter {

    protected AbstractAsmPrinter() {}

    public static Layouter layouter(LogicPrinter sp) {
	return sp.getLayouter();
    }

    public static void markStartSub(LogicPrinter sp) {
	sp.markStartSub();
    }

    public static void markEndSub(LogicPrinter sp) {
	sp.markEndSub();
    }

    public static void startTerm(LogicPrinter sp, int size) {
	sp.startTerm(size);
    }

    public static void maybeParens(LogicPrinter sp, Term t, int ass) 
	throws IOException
    {
	sp.maybeParens(t, ass);
    }

}
