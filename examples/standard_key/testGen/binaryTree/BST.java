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

public class BST{

    private /*@spec_public@*/ Node root;

    /*@ public normal_behavior
      @ requires (\forall Node n; n!=null; 
      @  (n.left!=null ==> 
      @    n.left!=null && n.left.value<n.value && n.left.parent == n) &&
      @  (n.right!=null ==>
      @    n.right!=null && n.right.value>n.value && n.right.parent == n));
      @ ensures contains(value) && consistencyCheck(root);
      @*/
    public void insert(int value){
	Node current = root;
	if(root == null){
	    root = new Node(value);
	}else{
	    while(current.value != value){
		if(current.value > value){
		    if(current.left == null){
			current.setLeft(new Node(value));
		    }
		    current = current.left;
		}else{
		    if(current.right == null){
			current.setRight(new Node(value));
		    }
		    current = current.right;
		}
	    }
	}
    }

    /*@ public normal_behavior
      @ requires (\forall Node n; n!=null; 
      @ (n.left!=null ==> 
      @   n.left!=null && n.left.value<n.value && n.left.parent == n &&
      @     (n.left.right!=null ==> n.left.right!=null &&
      @                             n.left.right.parent == n.left &&
      @                             n.left.right.value > n.left.value && 
      @                             n.left.right.value < n.value)) && 
      @ (n.right!=null ==>
      @   n.right!=null && n.right.value>n.value && n.right.parent == n &&
      @     (n.right.left!=null ==> n.right.left!=null  &&
      @                             n.right.left.parent == n.right && 
      @                             n.right.left.value < n.right.value && 
      @                             n.right.left.value > n.value)));
      @   //public normal_behavior
      @   //requires consistencyCheck(root);
      @   //ensures !contains(value) && consistencyCheck(root);
      @*/
    public void remove(int value){
	Node n = get(value); 
	if(n != null){
	    if(n.left == null){
		if(n == root){
		    root = n.right;
		    if(root!=null){
			root.parent = null;
		    }
		}else{
		    if(n.parent!=null){
			if(n.parent.left == n){
			    n.parent.setLeft(n.right);
			}else{
			    n.parent.setRight(n.right);
			}
		    }
		}
	    }else{
		Node current = n.left;
		while(current.right != null){
		    current = current.right;
		}
		if(n.parent!=null && current.parent != n){
		    current.parent.setRight(current.left);
		    current.setLeft(n.left);
		}
		current.setRight(n.right);
		current.setParent(n.parent);
	    }
	    // reestablish invariant
	    n.left = null;
	    n.right = null;
	    n.parent = null;
	}
    }

    public /*@pure@*/ boolean contains(int value){
	return get(value) != null;
    }

    private /*@pure@*/ Node get(int value){
	Node current = root;
	while(current != null && current.value != value){
	    if(current.value > value){
		current = current.left;
	    }else{
		current = current.right;
	    }
	}
	return current;
    }

    public /*@pure@*/ boolean consistencyCheck(Node n){
	return n==null || 
	    (n.left==null || (n.left.value<n.value && n.left.parent==n))
	    && 
	    (n.right==null || (n.right.value>n.value && n.right.parent==n))
	    && consistencyCheck(n.right) && consistencyCheck(n.left);
    }

}
