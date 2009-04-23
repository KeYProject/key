// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class MySubIterator extends MyIterator {
 
    public MySubIterator(Object o) {
	super(null);
    }


    public Object violate() {
	//violates encapsulation by returning a node which may be part of a list
        return pos.next.next;
    }
}
