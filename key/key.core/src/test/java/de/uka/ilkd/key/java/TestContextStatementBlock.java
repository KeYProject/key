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

package de.uka.ilkd.key.java;

import de.uka.ilkd.key.java.declaration.LocalVariableDeclaration;
import de.uka.ilkd.key.java.expression.operator.PostIncrement;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.logic.PosInProgram;
import de.uka.ilkd.key.rule.TacletForTests;
import org.junit.jupiter.api.AfterEach;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.key_project.util.ExtList;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;


public class TestContextStatementBlock {
    
    JavaBlock blockOne;

    @BeforeEach
	public void setUp() {
	JavaInfo ji = TacletForTests.javaInfo();
	Services services = TacletForTests.services();
	Recoder2KeY c2k 
	    = new Recoder2KeY(services,ji.getKeYProgModelInfo().getServConf(),
			      ji.rec2key(),
			      new NamespaceSet(),
			      services.getTypeConverter());
	blockOne
	    = c2k.readBlock("{int a=1; {int b=3; b++;} a++;}",
			   c2k.createEmptyContext());	
	
    }
    
    @AfterEach
	public void tearDown() {
        blockOne = null;
    }

	@Test
    public void testContextTermInstantiation() {
	ExtList statementList = new ExtList();
	StatementBlock stContainer = (StatementBlock) blockOne.program();
	int size = stContainer.getChildCount();
		assertEquals(3, size, "Wrong size. Should have only 3 children");
	PosInProgram prefixEnd = PosInProgram.TOP.down(0);
	assertTrue(PosInProgram.getProgramAt(prefixEnd, blockOne.program())
			instanceof
			LocalVariableDeclaration, "Prefix should end with an assignment");
	PosInProgram suffixStart = PosInProgram.TOP.down(2);
	assertTrue(PosInProgram.getProgramAt(suffixStart, blockOne.program())
			instanceof
			PostIncrement, "Suffix should start with an ++");
	for (int i=size-2; i>=1; i--) {
	    statementList.add
		(stContainer.getChildAt(i));
	}	
		
    }


}