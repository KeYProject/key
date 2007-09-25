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
