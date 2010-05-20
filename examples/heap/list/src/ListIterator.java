interface ListIterator {
    
    //@ public model instance List list;
    //@ public model instance int pos;
    
    
    /*@ normal_behaviour
      @   accessible this.*, list.footprint;
      @   ensures \result == pos < list.size();
      @*/
    public /*@pure@*/ boolean hasNext();
    
    
    /*@ normal_behaviour
      @   requires pos < list.size();
      @   assignable this.*;
      @   ensures \result == list.get(\old(pos));
      @   ensures pos == \old(pos) + 1;
      @ also exceptional_behaviour
      @   requires pos >= list.size();
      @   signals_only IndexOutOfBoundsException;
      @*/
    public /*@nullable@*/ Object next();
}
