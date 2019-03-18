import java.util.Iterator;

public class IntIterator implements Iterator {

    private final IntLinkedList list;
    private /*@nullable@*/ IntNode next;
    
    //@ ghost \seq nodeseq;
    //@ ghost \seq seq;
    
    //@ public instance invariant nodeseq == list.nodeseq[0 .. (nodeseq.length - 1)];
    //@ public instance invariant seq == list.seq[0 .. (seq.length - 1)];

    //@ public instance invariant nodeseq.length <= list.nodeseq.length;
    //@ public instance invariant seq.length <= list.seq.length;
    //@ public instance invariant seq.length == nodeseq.length;

    //@ public instance invariant next != null ==> next == nodeseq[nodeseq.length - 1];
    //@ public instance invariant next != null ==> next.data == seq[seq.length - 1];
    
    //@ public instance invariant seq.length == list.seq.length <==> next == null;

    public IntIterator(IntLinkedList list) {
        this.list = list;
        
        next = list.first;
        //@ set nodeseq = \seq_concat(nodeseq, \seq_singleton(next));
        //@ set seq = \seq_concat(seq, \seq_singleton(next.data));
    }

    /*@ public normal_behavior
      @ ensures \result == (next != null);
      @ assignable \strictly_nothing;
      @*/
    public boolean hasNext() {
        return next != null;
    }

    /*@ public normal_behavior
      @ requires next != null;
      @ ensures \result.intValue() == \old(next).data;
      @ ensures seq.length == \old(seq.length) + 1;
      @ assignable \nothing;
      @*/
    public Integer next() {
        int result = next.data;
        
        next = next.next;
        //@ set nodeseq = \seq_concat(nodeseq, \seq_singleton(next));
        //@ set seq = \seq_concat(seq, \seq_singleton(next.data));
        
        return Integer.valueOf(result);
    }
}
