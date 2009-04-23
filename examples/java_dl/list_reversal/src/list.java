// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
public class list {
    public list next, prev;

    public static list rev(list a) {
	list res = null;
	while (a != null) {
	    res = a;
	    final list t = a.next;
	    a.next = a.prev;
	    a.prev = t;
	    a = t;
	}
	return res;
    }
}
