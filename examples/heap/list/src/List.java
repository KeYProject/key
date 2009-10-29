interface List {
    
    //@ instance model \set footprint;
    //@ depends footprint: footprint;
    //@ depends <inv>: footprint;
    
    
    /*@ normal_behaviour
      @   assignable footprint;
      @   ensures size() == \old(size()) + 1;
      @   ensures get(size() - 1) == o;
      @   ensures (\forall int i; 0 <= i && i < size() - 1; get(i) == \old(get(i)));
      @   ensures \newElemsFresh(footprint);
      @*/    
     public void add(/*@nullable@*/ Object o);
     
     
    /*@ normal_behaviour
      @   accessible footprint;
      @   ensures \result == (\exists int i; 0 <= i && i < size(); get(i) == o);
      @*/
    public /*@pure@*/ boolean contains(/*@nullable@*/ Object o);  
    
    
    /*@ normal_behaviour
      @   requires 0 <= index && index < size(); 
      @   accessible footprint;
      @   ensures \result == get(index);
      @
      @ also exceptional_behaviour
      @   requires index < 0 || size() <= index;
      @   signals_only IndexOutOfBoundsException;
      @*/
    public /*@pure nullable@*/ Object get(int index);
    
    
    /*@ normal_behaviour
      @   ensures \fresh(\result);
      @   ensures \result.list == this;
      @   ensures \result.pos == 0;
      @*/
    public /*@pure@*/ ListIterator iterator();
    
    
    /*@ normal_behaviour
      @   requires (\forall int i; 0 <= i && i < size(); get(i) != o);
      @   assignable \nothing;
      @ also normal_behaviour
      @   requires (\exists int i; 0 <= i && i < size(); get(i) == o);
      @   assignable footprint;
      @   ensures size() == \old(size()) - 1;
      @   ensures (\exists int i; 0 <= i && i < \old(size()) && \old(get(i)) == o;
      @              (\forall int j; 0 <= j && j < i; get(j) == \old(get(j)))
      @              && (\forall int k; i <= k && k < size(); get(k) == \old(get(k+1))));
      @   ensures \newElemsFresh(footprint);
      @*/     
    public void remove(/*@nullable@*/ Object o);
    
    
    /*@ normal_behaviour
      @   accessible footprint;
      @   ensures \result == size();
      @*/
    public /*@pure@*/ int size();
}
