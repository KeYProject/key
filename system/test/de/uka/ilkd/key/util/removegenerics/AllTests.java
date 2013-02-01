// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


package de.uka.ilkd.key.util.removegenerics;

import junit.framework.Test;
import junit.framework.TestSuite;

public class AllTests {

    public static Test suite() {
        TestSuite suite = new TestSuite("Test for de.uka.ilkd.key.util.removegenerics");
        //$JUnit-BEGIN$
        suite.addTestSuite(TestMultipleBounds.class);
        suite.addTestSuite(TestTypeReference.class);
        suite.addTestSuite(TestMemberReference.class);
        suite.addTestSuite(TestMethodDeclaration.class);
        suite.addTestSuite(TestClassDeclaration.class);
        //$JUnit-END$
        return suite;
    }

}
