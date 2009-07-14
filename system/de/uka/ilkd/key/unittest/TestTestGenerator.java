// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
package de.uka.ilkd.key.unittest;

import junit.framework.TestCase;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.JavaInfo;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.rule.TacletForTests;

public class TestTestGenerator extends TestCase {

    private JavaInfo javaInfo;
    private Profile old;
    
    public TestTestGenerator(String name) {
        super(name);
    }

    public void setUp() {
	old = ProofSettings.DEFAULT_SETTINGS.getProfile();
	ProofSettings.DEFAULT_SETTINGS.setProfile(TacletForTests.profile);
        TacletForTests.lastFile = null;
	TacletForTests.parse();
        javaInfo = TacletForTests.getJavaInfo();
    }
    
    public void tearDown() {
	ProofSettings.DEFAULT_SETTINGS.setProfile(old);
        TacletForTests.lastFile = null;
        TacletForTests.parse();
    }
    
    public void testJUnitClassesAvailable(){
        KeYJavaType testCase = javaInfo.getKeYJavaTypeByClassName("junit.framework.TestCase");
        KeYJavaType testSuite = javaInfo.getKeYJavaTypeByClassName("junit.framework.TestSuite");
        KeYJavaType stringBuffer = javaInfo.getKeYJavaTypeByClassName("java.lang.StringBuffer");
        assertTrue(testCase!=null && testSuite!=null && stringBuffer!=null);
    }
    
}
