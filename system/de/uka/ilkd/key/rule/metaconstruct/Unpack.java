// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.rule.metaconstruct;

import de.uka.ilkd.key.java.ProgramElement;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.java.StatementBlock;
import de.uka.ilkd.key.java.statement.For;
import de.uka.ilkd.key.java.statement.LoopInit;
import de.uka.ilkd.key.rule.inst.SVInstantiations;
import de.uka.ilkd.key.util.Debug;

public class Unpack extends ProgramMetaConstruct {


    /** creates a typeof ProgramMetaConstruct 
     * @param loop the instance of expression contained by 
     * the meta construct 
     */
    public Unpack(For loop) {
	super("unpack", loop); 
    }

    /** 
     * performs the program transformation needed for symbolic
     * program transformation 
     * @return the transformated program
     */
    public ProgramElement symbolicExecution(ProgramElement pe,
	    Services services,
	    SVInstantiations svInst) {
	Debug.assertTrue(pe instanceof For, 
		"Unpack cannot handle " + pe);
	final For astFor  = (For)pe;
	final Statement[] loopInitStatementList = 
	    new Statement[astFor.getInitializers().size() + 1];
	for (int i = 0; i<loopInitStatementList.length-1; i++) {
	    loopInitStatementList[i] = 
		astFor.getInitializers().get(i);
	}

	loopInitStatementList
	[loopInitStatementList.length - 1] = new For((LoopInit)null, 
		astFor.getGuard(), 
		astFor.getIForUpdates(), 
		astFor.getBody());
	return new StatementBlock(loopInitStatementList);
    }
}
