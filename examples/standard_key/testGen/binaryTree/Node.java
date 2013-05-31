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

public class Node{
    
    public int value;

    public Node parent = null;
    public Node left = null;
    public Node right = null;

    public Node(int value){
	this.value = value;
    }
    
    public void setLeft(Node l){
	left = l;
	if(l!=null){
	    l.parent = this;
	}
    }

    public void setRight(Node r){
	right = r;
	if(r!=null){
	    r.parent = this;
	}
    }

    public void setParent(Node p){
	if(p!=null){
	    if(p.value > value){
		p.setLeft(this);
	    }else{
		p.setRight(this);
	    }
	}else{
	    parent = null;
	}
    }

    public String toString(){
	return (new Integer(value)).toString();
    }

}
