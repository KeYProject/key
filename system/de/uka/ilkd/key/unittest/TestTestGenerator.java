// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.rule.TacletForTests;

public class TestTestGenerator extends TestCase {

    private JavaInfo javaInfo;
    
    public TestTestGenerator(String name) {
        super(name);
    }

    public void setUp() {
        TacletForTests.parse();
        javaInfo = TacletForTests.getJavaInfo();
    }
    
    public void testJUnitClassesAvailable(){
        KeYJavaType testCase = javaInfo.getKeYJavaTypeByClassName("junit.framework.TestCase");
        KeYJavaType testSuite = javaInfo.getKeYJavaTypeByClassName("junit.framework.TestSuite");
        KeYJavaType stringBuffer = javaInfo.getKeYJavaTypeByClassName("java.lang.StringBuffer");
        assertTrue(testCase!=null && testSuite!=null && stringBuffer!=null);
    }
    
}
