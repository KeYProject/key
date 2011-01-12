// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2010 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.java.visitor;

import java.util.HashSet;
import java.util.Iterator;
import java.util.Set;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.Recoder2KeY;
import de.uka.ilkd.key.logic.JavaBlock;
import de.uka.ilkd.key.logic.Named;
import de.uka.ilkd.key.logic.NamespaceSet;
import de.uka.ilkd.key.rule.TacletForTests;

public class TestDeclarationProgramVariableCollector  extends TestCase {

    // some non sense java blocks with lots of statements and expressions
    private static String[] jblocks=new String[]{
	"{ int j1 = 0; int j2, j3, j4 = 0;}",
	"{ int j1; { int j2; } { int j3; } for (int j4; j4=0; j4++) {} int j5; }",
	"{ int j0; { { { { {  int j1; } int j2; } int j3;} int j4; } } }"
    };

    // names of variables expected to be collected in jblocks
    private static String[][] expectedVars = new String[][]{
	{"j1", "j2", "j3", "j4"},
	{"j1", "j5"},
	{"j0"}
    };


    private static JavaBlock[] test_block = new JavaBlock[jblocks.length];

    private static int testCases = 0;
    private static int down = 0;
    
    public TestDeclarationProgramVariableCollector(String name) {
	super(name);
        testCases++;
    }


    public void setUp() {
        if (down != 0) return;
        final Recoder2KeY r2k = new Recoder2KeY(TacletForTests.services(), new NamespaceSet());
	for (int i = 0; i < jblocks.length; i++) {
	    test_block[i] = r2k.readBlockWithEmptyContext(jblocks[i]);
	}
    }
    
    public void tearDown() {
        down++;
        if (down < testCases) return;
        test_block = null;    
    }
    
    private HashSet toNames(Set programVariables) {
	HashSet result = new HashSet();
        for (Object programVariable : programVariables) {
            String name = "" + ((Named) programVariable).name();
            if (result.contains(name)) {
                System.out.println("Warning: Program variables have same name." +
                        " Probably unsane test case");
            }
            result.add(name);
        }
	return result;
    }
    

    public void testVisitor() {
	DeclarationProgramVariableCollector dpvc;
	for (int i = 0; i < jblocks.length; i++) {
	    dpvc = new DeclarationProgramVariableCollector(test_block[i].program(), 
                                                           TacletForTests.services());
	    dpvc.start();
	    HashSet names = toNames(dpvc.result());


	    assertTrue("Too many variables collected. Collected:" + 
		       dpvc.result() + " in " + jblocks[i], 
		       dpvc.result().size() <= expectedVars[i].length);


	    for (int j = 0; j < expectedVars[i].length; j++) {
		assertTrue("Missing variable: "+expectedVars[i][j] + " of " + jblocks[i], 
			   names.contains(expectedVars[i][j]));
	    }	    
	}
    }

}
