// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java;

import junit.framework.TestCase;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.ExtList;


public class TestContextStatementBlock extends TestCase {
    
    JavaBlock blockOne;

    public TestContextStatementBlock(String name) {
	super(name);
    }

    public void setUp() {
	JavaInfo ji = TacletForTests.javaInfo();
	Recoder2KeY c2k 
	    = new Recoder2KeY(ji.getKeYProgModelInfo().getServConf(),
			      ji.rec2key(),
			      new NamespaceSet(),
			      TacletForTests.services().getTypeConverter());
	blockOne
	    = c2k.readBlock("{int a=1; {int b=3; b++;} a++;}",
			   c2k.createEmptyContext());	
	
    }
    
    public void tearDown() {
        blockOne = null;
    }
    
    public void testContextTermInstantiation() {
	ExtList statementList = new ExtList();
	StatementBlock stContainer = (StatementBlock) blockOne.program();
	int size = stContainer.getChildCount();
	assertTrue("Wrong size. Should have only 3 children", size==3);
	PosInProgram prefixEnd = PosInProgram.TOP.down(0);
	assertTrue("Prefix should end with an assignment", 
		   PosInProgram.getProgramAt(prefixEnd, blockOne.program()) 
		   instanceof 
		   de.uka.ilkd.key.java.declaration.LocalVariableDeclaration);
	PosInProgram suffixStart = PosInProgram.TOP.down(2);
	assertTrue("Suffix should start with an ++", 
		   PosInProgram.getProgramAt(suffixStart, blockOne.program()) 
		   instanceof 
		   de.uka.ilkd.key.java.expression.operator.PostIncrement);
	for (int i=size-2; i>=1; i--) {
	    statementList.add
		((Statement)stContainer.getChildAt(i));
	}	
		
    }


}
