// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//normal basic list
public class MyList {

    private MyNode head;

    public void prepend(Object data) {
        MyNode newHead = new MyNode(data);
        newHead.next = this.head;
        head = newHead;
    }
    
    public MyIterator iterator() {
	return new MyIterator(head);
    }
}
