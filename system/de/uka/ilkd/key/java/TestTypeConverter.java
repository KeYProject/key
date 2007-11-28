// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2007 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.java;

import junit.framework.TestCase;
import de.uka.ilkd.key.java.expression.literal.StringLiteral;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.rule.TacletForTests;

public class TestTypeConverter extends TestCase {
    
    static String[][] stringTests ={
        { "\"test\"",
        "cat(Z(6(1(1(#)))),cat(Z(1(0(1(#)))),cat(Z(5(1(1(#)))),cat(Z(6(1(1(#)))),epsilon))))"},
        {"\"\"","epsilon"}
    };
    
    
    private Services serv;
    private TypeConverter tc;
    
    
    public TestTypeConverter(String name) {
	super(name);
    }

    public void setUp() {	
	TacletForTests.parse();
        serv = TacletForTests.services();
        serv.setNamespaces(TacletForTests.getNamespaces());
        tc = serv.getTypeConverter();
    }

    public void tearDown() {
	serv = null;
	tc = null;
    }

    
    public void testStringConverter() {
        Term t, match;
        for (int i = 0; i < stringTests.length; i++) {
            t = tc.convertToLogicElement(
                    new StringLiteral(stringTests[i][0]));
            match = TacletForTests.parseTerm(stringTests[i][1], serv
                    .getNamespaces());
            assertTrue("Expected that StringLiteral " + stringTests[i][0]
                    + " is translated to " + stringTests[i][1], match.equals(t));

            Expression stringExpr = TypeConverter.stringConverter.translateTerm(match,null); 
            assertTrue("Expected that Term " + stringTests[i][1]
                           + " is translated to " + stringTests[i][0], 
                           stringExpr.equals(new StringLiteral(stringTests[i][0])));    
       }
    }

}
