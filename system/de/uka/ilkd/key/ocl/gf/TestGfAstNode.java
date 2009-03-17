// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//Copyright (c) Hans-Joachim Daniels 2005
//
//This program is free software; you can redistribute it and/or modify
//it under the terms of the GNU General Public License as published by
//the Free Software Foundation; either version 2 of the License, or
//(at your option) any later version.
//
//This program is distributed in the hope that it will be useful,
//but WITHOUT ANY WARRANTY; without even the implied warranty of
//MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
//GNU General Public License for more details.
//
//You can either finde the file LICENSE or LICENSE.TXT in the source 
//distribution or in the .jar file of this application

package de.uka.ilkd.key.ocl.gf;

import junit.framework.Test;
import junit.framework.TestCase;
import junit.framework.TestSuite;

public class TestGfAstNode extends TestCase {
        public static Test suite() { 
                TestSuite suite= new TestSuite(); 
                suite.addTest(new TestGfAstNode()); 
                return suite;
        }
        
        public static void main(String args[]) { 
                junit.textui.TestRunner.run(suite());
        }
        
        public void setUp() {
                //nothing to be done here
        }
        
        public void testConstructor() {
                String[] lines = {"?1 : Sent",
                                "Two : Instance Integer",
                                "?3 : Instance (Collection (?{this:=this{-0-}}))",
                                "NOPACKAGEP_StartC_Constr : Constraint {Constraint<>NOPACKAGEP_StartC_Constr (\\this -> invCt ?)}",
                                "\\(this : VarSelf NOPACKAGEP_StartC) -> invCt : ClassConstraintBody",
                                "\\(x_0 : Instance Integer) -> ?6 : Sent",
                                "\\(selfGF : VarSelf NOPACKAGEP_PayCardC),(amount : Instance Integer) -> preC : OperConstraintBody",
                                "\\(selfGF : VarSelf NOPACKAGEP_PayCardC),(amount : Instance Integer) -> ?0 : OperConstraintBody"
                };
                String[] funs = {"?1",
                                "Two",
                                "?3",
                                "NOPACKAGEP_StartC_Constr",
                                "invCt",
                                "?6",
                                "preC",
                                "?0" 
                };
                String[] types = {"Sent",
                                "Instance Integer",
                                "Instance (Collection (?{this:=this{-0-}}))",
                                "Constraint",
                                "ClassConstraintBody",
                                "Sent",
                                "OperConstraintBody",
                                "OperConstraintBody" 
                };
                String[] constraints = {"",
                                "",
                                "",
                                "{Constraint<>NOPACKAGEP_StartC_Constr (\\this -> invCt ?)}",
                                "",
                                "",
                                "",
                                "",
                                ""
                };
                for (int i = 0; i < lines.length; i++) {
                        //System.out.println("* " + lines[i]);
                        GfAstNode gfa = new GfAstNode(lines[i]);
                        assertTrue("  fun mismatch: expected '" + funs[i] + "', got '" + gfa.getFun() + "'", gfa.getFun().equals(funs[i]));
                        assertEquals(gfa.getType(), types[i]);
                        assertEquals(gfa.constraint, constraints[i]);
                }
        }
}

