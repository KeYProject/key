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

//normal basic iterator, except for the violate() method
public class MyIterator {

    protected MyNode pos;

    public MyIterator(MyNode n) {
	pos = n;
    }

    public boolean hasNext() {
	return pos != null;
    }

    public Object next() {
	Object posData = pos.data;
	pos = pos.next;
	return posData;
    }

    public Object violate() {
	//this does not do anything bad, but MySubIterator overrides it with 
	//an implementation that does
        return (hasNext() ? next() : null);
    }
}
