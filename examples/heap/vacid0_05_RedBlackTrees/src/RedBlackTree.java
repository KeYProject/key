package vacid0.redblacktree;

/**
 * Implementation of a red-black tree.
 * Specification uses a ghost field of type \seq to have an abstract view on the tree.
 * @author bruns
 *
 */
public class RedBlackTree implements AbstractMap {

    private int deefolt;
    //@ represents defaultValue = deefolt;

    private Node root;
    //@ invariant !root.isRed;

    /*@ represents contents \such_that (\forall int i; 0 <= i;
      @            contents[i] == (get(i) == Node.NIL ? deefolt : get(i).value));
      @*/
    
    //@ ghost \seq theNodes;
    
    public RedBlackTree (int d){
        //@ set theNodes = \seq_empty;
        deefolt = d;
        root = Node.NIL;
    }
    

    // specified by interface
    public void replace (int key, int value){
        Node x = get(key);
        if (x == Node.NIL) {
            final  Node n = new Node(key,value);
            //@ set theNodes = \seq_concat(theNodes,\seq_singleton(n));
            insert(n);
        }
        else x.value = value;  
    }

    // specified by interface
    public void remove (int key){
        final Node n = get(key);
        if (n != Node.NIL) {
            //@ set theNodes = \seq_concat(\seq_sub(theNodes,0,\indexOf(theNodes,n) -1),\seq_sub(theNodes,\indexOf(theNodes,n)+1, \seq_length(theNodes)-1));
            removeNode(n);
        }
    }

    private void removeNode(Node n) {
        // TODO Auto-generated method stub
        
    }


    // specified by interface
    public int lookup (int key){
        Node x = get(key);
        if (x == Node.NIL)
            return deefolt;
        else return x.value;
    }
    
    //@ ensures (\exists int i; 0 <= i && i < theNodes.length; ((Node)theNodes[i]).key == key) ? \result.key == key : \result == Node.NIL;
    private /*@ pure @*/ Node get(int key){
        Node x = root;
        //@ ghost \seq visited = \seq_empty;
        
        /*@ decreasing x.height;
          @ maintaining 0 <= x.height && x.height <= root.height;
          @ maintaining (\forall int i; 0 <= i && i < visited.length; ((Node)visited[i]).key != key);
          @ assignable x;
          @*/
        while (x != Node.NIL && x.key != key){
            //@ set visited = \seq_concat(visited,\singleton(x));
            if (key < x.key)
                x = x.left;
            else x = x.right;
        }
        return x;
    }
   
    //@ requires z != Node.NIL;
    private void insert (Node z){
        Node x = root;
        Node y = Node.NIL;
        while (x != Node.NIL){
            y = x;
            if (z.key < x.key)
                x = x.left;
            else x = x.right;
        }
        //@ set z.height = 1;
        z.parent = y;
        if (y == Node.NIL)
            root = z;
        else if (z.key < y.key)
            y.left = z;
        else y.right = z;
        z.isRed = true;
        insertFix(z);
    }


    private void insertFix(Node z) {
        while (z.parent.isRed) {
            if (z.parent == z.parent.parent.left) {
                Node y = z.parent.parent.right;
                if (y.isRed) {
                    z.parent.isRed = false;
                    y.isRed = false;
                    z.parent.parent.isRed = true;
                    z = z.parent.parent;
                } else {
                    if (z == z.parent.right) {
                        z = z.parent;
                        z.leftRotate(this);
                    }
                    z.parent.isRed = false;
                    z.parent.parent.isRed = true;
                    z.parent.parent.rightRotate(this);
                }
            } else {
                Node y = z.parent.parent.left;
                if (y.isRed) {
                    z.parent.isRed = false;
                    y.isRed = false;
                    z.parent.parent.isRed = true;
                    z = z.parent.parent;
                } else {
                    if (z == z.parent.left) {
                        z = z.parent;
                        z.rightRotate(this);
                    }
                    z.parent.isRed = false;
                    z.parent.parent.isRed = true;
                    z.parent.parent.leftRotate(this);
                }
            }
        }
        root.isRed = false;
    }


    //@ ensures root == y;
    //@ assignable root;
    void setRoot(Node y) {
        root = y;
    }

    

}
