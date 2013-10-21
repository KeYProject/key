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

package de.uka.ilkd.key.logic;

import junit.framework.TestCase;

public class TestName extends TestCase {

    protected void setUp() throws Exception {
        super.setUp();
    }

    public void testEquals (){
        Name n = new Name("test");
        Name m = new Name(new String("test"));
        assertEquals(n,m);
    }
}