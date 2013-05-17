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

package de.uka.ilkd.key.util;

import junit.framework.TestCase;

public class TestLexicographicComparator extends TestCase {

    
    public void testCompareInt() {
        Integer[] a = {3,4};
        Integer[] b = {1,7};
        final LexicographicComparator<Integer> lcc = new LexicographicComparator<Integer>();
        assertEquals(-1,lcc.compare(a,b));
        b = new Integer[]{3,4,0};
        assertEquals(1,lcc.compare(a, b));
        a = new Integer[]{3,4,0};
        assertEquals(0,lcc.compare(a,b));
    }
}