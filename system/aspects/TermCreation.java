// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2003 Universitaet Karlsruhe, Germany
//                         and Chalmers University of Technology, Sweden          
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//

package aspects;

import de.uka.ilkd.key.logic.*;

/** An aspect that detects illegal calls to constructors of the 
 * subclasses of de.uka.ilkd.key.logic.Term.  Calls from within
 * the test class TestTermFactory are OK.
 */
public aspect TermCreation extends KeYAspect {

    declare warning: 
	call(Term+.new(..))
	&& !within(TermFactory) && !within(TestTermFactory):
	"Warning: Constructor of a sub-class of Term called outside TermFactory";

}

