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

public class TestUtils extends TestCase {
        public static Test suite() { 
                TestSuite suite= new TestSuite(); 
                suite.addTest(new TestGfAstNode()); 
                return suite;
        }
        
        public static void main(String args[]) { 
                junit.textui.TestRunner.run(suite());
        }
        
        public void setUp() { 
                //testing a static method, no setup needed
        }
        
        public void testReplaceAll() {
                //perhaps not comprehensive ...
                String[] originals = {"\\\\$fgg",
                                "__\\$__",
                                "__\\>__"
                };
                String[] toReplaces = {"\\\\",
                                "\\\\",
                                "\\>"
                };
                String[] replacements = {"\\",
                                "\\",
                                ">"
                };
                String[] results = {"\\$fgg",
                                "__\\$__",
                                "__>__"
                };
                
                for (int i = 0; i < originals.length; i++) {
                        assertEquals(Utils.replaceAll(originals[i], toReplaces[i], replacements[i]), results[i]);
                }
               
        }
        
        public void testIndexOfNotEscaped() {
                final String[] lines = {"abcGHFb",
                                "abcGHFb",
                                "abcGHFabcb",
                                "abcGHFb",
                                "\\abcGHF",
                                "abc\\GHFb",
                                "abc\\GHFabcGHF",
                                "abc\\GHF\\ghcGHC\\GHC"
                };
                final String[] searchStrings = {"abc",
                                "GHF",
                                "abc",
                                "hhh",
                                "abc",
                                "GHF",
                                "GHF",
                                "GHC" 
                };
                final int[] positions = {0,
                                3,
                                0,
                                -1,
                                -1,
                                -1,
                                10,
                                11 
                };
                
                for (int i = 0; i < lines.length; i++) {
                        assertTrue("wrong unescaped index of '" + searchStrings[i] + "' in '" + lines[i] + "' : " + Utils.indexOfNotEscaped(lines[i], searchStrings[i]) + " instead of " + positions[i], Utils.indexOfNotEscaped(lines[i], searchStrings[i]) == positions[i]);
                }
        }
        
        public void testRemoveQuotations() {
                final String[] orig = {"hallo",
                                "ha\\\"llo", //should be ha\"llo!
                                "ha\"ll\"o",
                                "h\"a\"l\"1\"o",
                                "h\"a\\\"ll\"o"
                };
                final String[] unqu = {"hallo",
                                "ha\\\"llo", //should be ha\"llo!
                                "hao",
                                "hlo",
                                "ho"
                };
                for (int i = 0; i < orig.length; i++) {
                        assertEquals(Utils.removeQuotations(orig[i]), unqu[i]);
                }
                
        }
        
        public void testCountOccurances() {
                final String[] orig = {"ass ;; dff",
                                "fds ;;; sdf;;",
                                "dssa;;;;sfsd;sd;",
                                "sdff;;;;;"
                };
                final int[] oc = {1, 2, 2, 2};
                final String toSearch = ";;";
                for (int i = 0; i < orig.length; i++) {
                        assertEquals(Utils.countOccurances(orig[i], toSearch), oc[i]);
                }
        }
}

