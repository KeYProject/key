class RedBlackTree implements AbstractMap {

    int deefolt;
    //@ represents defaultValue = deefolt;

    /*@ nullable @*/ Node root;
    //@ invariant root == null || !root.isRed;

    RedBlackTree (int d){
        deefolt = d;
    }

    void replace (int key, int value){}

    void remove (int key){}

    int lookup (int key){}
    

}
