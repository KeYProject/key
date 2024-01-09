final class LinkedList implements List {

    private /*@nullable@*/ Node first;
    private /*@nullable@*/ Node last;
    private int size;

    /*@ private ghost \seq nodeseq; */
    
    /*@
      @ private invariant footprint == \set_union(this.*,
      @      (\infinite_union int i; 0<=i && i<size; ((Node)nodeseq[i]).*));
      @
      @ private invariant (\forall int i; 0<=i && i<size; 
      @         ((Node)nodeseq[i]) != null  // this implies \typeof(nodeseq[i]) == \type(Node)
      @      && ((Node)nodeseq[i]).data == (\bigint)seq[i] 
      @      && (\forall int j; 0<=j && j<size; (Node)nodeseq[i] == (Node)nodeseq[j] ==> i == j)
      @      && ((Node)nodeseq[i]).next == (i==size-1 ? null : (Node)nodeseq[i+1]));
      @
      @ private invariant first == (size == 0 ? null : (Node)nodeseq[0]);
      @ private invariant last == (size == 0 ? null : (Node)nodeseq[size-1]);
      @
      @ private invariant size == seq.length && size == nodeseq.length;
      @*/

    /*@ normal_behaviour
      @   ensures seq == \seq_empty;
      @   ensures \fresh(footprint);
      @*/
    public /*@pure@*/ LinkedList() {
        //@ set footprint = \all_fields(this);
        //@ set seq = \seq_empty;
        first = null;
    }

    public int size() {
        return size;
    }

    public int get(int index) {
        if(index < 0 || size <= index) {
            throw new IndexOutOfBoundsException();
        }

        Node node = first;
        /*@ loop_invariant 0 <= i && i <= index && node == (Node)nodeseq[i];
          @ assignable \strictly_nothing;
          @ decreases index - i;
          @*/
        for(int i = 0; i < index; i++) {
            node = node.next;
        }

        return node.data;
    }

    public int find(int value) {
        if(size == 0) {
            return -1;
        }

        Node node = first;
        /*@ loop_invariant 0 <= i && i <= size 
          @   && (i < size ==> node == (Node)nodeseq[i])
          @   && (i == size ==> node == null)
          @   && (\forall int x; 0 <= x && x < i; (\bigint)seq[x] != value);
          @ assignable \strictly_nothing;
          @ decreases size - i;
          @*/
        for(int i = 0; i < size; i++) {
            if(node.data == value) {
                return i;
            }
            node = node.next;
        }

        return -1;
    }

    /*@ private normal_behaviour
      @   ensures \fresh(\result);
      @   ensures \result.data == o;
      @   ensures \result.next == null;
      @   assignable \nothing;
      @*/
    private Node newNode(int o) {
        Node result = new Node();
        result.data = o;
        return result;
    }

    public void add(int value) {
        Node node = newNode(value);
        if(size == 0) {
            first = node;
            last = node;
        } else {
            last.next = node;
            last = last.next;
        }
        //@ set seq = \seq_concat(seq, \seq_singleton(value));
        //@ set nodeseq = \seq_concat(nodeseq, \seq_singleton(node));
        //@ set footprint = \set_union(footprint, \all_fields(node));
        size++;
    }
}
