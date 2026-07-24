public interface List {

    //@ public ghost instance \locset footprint;
    //@ public ghost instance \seq seq;

    //@ public instance invariant \subset(\singleton(this.seq), footprint);
    //@ public instance invariant \subset(\singleton(this.footprint), footprint);
    //@ accessible \inv: footprint;

    /*@ public normal_behaviour
      @   requires 0 <= index && index < seq.length;
      @   accessible footprint;
      @   ensures \result == (\bigint)seq[index];
      @*/
    public /*@pure@*/ int get(int index);

    /*@ public normal_behaviour
      @   accessible footprint;
      @   ensures \result == seq.length;
      @*/
    public /*@pure@*/ int size();

    /*@ public normal_behaviour
      @   assignable footprint;
      @   ensures seq == \old(seq) + \seq_singleton(o);
      @   ensures \new_elems_fresh(footprint);
      @*/
    public void add(int o);

    /*@ public normal_behaviour
      @   requires (\forall int x; (\forall int y; 0<=x<y<seq.length; (\bigint)seq[x] <= (\bigint)seq[y]));
      @   ensures -1 <= \result < seq.length;
      @   ensures (\exists int idx; 0<=idx<seq.length; (\bigint)seq[idx] == value) ?
      @      \result >= 0 && (\bigint)seq[\result] == value : \result == -1;
      @   assignable \nothing;
      @*/
    public int find(int value);
}