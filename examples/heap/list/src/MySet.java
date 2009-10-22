final class MySet {
    
    //@ instance model \set footprint;
    //@ depends footprint: footprint;
    //@ depends <inv>: footprint;
    
    private List list;
       
    //@ represents footprint <- this.*, list.footprint;

    
    /*@ invariant list.<inv> && list.size() >= 0
      @           && \disjoint(list.footprint, this.*)
      @           && (\forall int x, y; 0 <= x && x < list.size() && 0 <= y 
      @                                   && y < list.size() && x != y; 
      @                                 list.get(x) != list.get(y));
      @*/
    
    
    /*@ normal_behaviour
      @   requires initial.<inv> && initial.size() >= 0;
      @   requires \disjoint(initial.footprint, this.*);
      @   requires (\forall int x, y; 0 <= x && x < initial.size() && 0 <= y 
      @                                && y < initial.size() && x != y; 
      @                               initial.get(x) != initial.get(y));
      @   ensures (\forall int x; 0 <= x && x < initial.size(); contains(initial.get(x)));
      @*/
    public /*@pure@*/ MySet(List initial) {
	this.list = initial;
    }
    
    
    /*@ normal_behaviour
      @   assignable footprint;
      @   ensures (\forall Object x; contains(x) == (\old(contains(x)) || o == x));
      @*/
    public void add(Object o) {
	if(!list.contains(o)) {
	    list.add(o);
	}
    }
    
    
    /*@ normal_behaviour
      @   requires l.<inv> && l.size() >= 0;
      @   requires \disjoint(l.footprint, footprint);      
      @   assignable footprint;
      @   ensures (\forall Object x; contains(x) == (\old(contains(x)) || l.contains(x)));
      @*/
    public void addAll(List l) {
	ListIterator it = l.iterator();
	/*@ loop_invariant 0 <= it.pos && it.pos < l.size()
	  @   && (\forall int x; 0 <= x && x < \old(list.size()) - 1; list.get(x) == \old(list.get(x)));
          @ assignable l.footprint;
	  @*/
	while(it.hasNext()) {
	    add(it.next());
	}
    }


    /*@ normal_behaviour
      @   ensures \result == contains(o);
      @*/
    public /*@pure@*/ boolean contains(Object o) {
	return list.contains(o);
    }
    
    
    //interactive proofs:
    //-Constructor (obvious quantifier instantiation)
    //-add (some relatively obvious quantifier instantiations [self.list.size()])
    //-contains (obvious quantifier instantiation)
    
    //not yet verified:
    //-addAll
}
