package CaseStudyUseMaps;

public interface Map2 {
    
    //@ public ghost instance \locset footprint;
    //@ public ghost instance \free map;
    
    //@ public instance invariant \subset(\singleton(this.map), footprint);
    //@ public instance invariant \subset(\singleton(this.footprint), footprint);
    
    /* @ public instance invariant (\forall Object o; 
     @ \dl_mapGet(map, o) instanceof Object || \dl_mapGet(map, o) == null );
     @*/
    
    /* @ public instance invariant (\forall Object o; 
     @ (\dl_inDomain(map, o) <==> (\dl_mapGet(map, o) != null )));
     @*/
    
    //@ public accessible \inv: footprint;
    
    // -----
    // Method signatures + specs
    // -----
    
    /*@ public normal_behaviour
    @ accessible footprint;
    @ ensures \result == (\dl_inDomain(map, o)?\dl_mapGet(map, o):null);
    @*/
    public /*@pure nullable@*/ Object get(Object o);

    /*@ public normal_behaviour
     @ accessible footprint;
     @   ensures \result == (map == \dl_mapEmpty());
     @*/
    public /*@pure@*/ boolean isEmpty();
    
    /*@ public normal_behaviour
     @ accessible footprint;
     @   ensures \result == (\sum Object key; \dl_inDomain(map,key); 1);
     @*/
    public /*@pure@*/ int size();

    /*@ public normal_behaviour
     @ accessible footprint;
     @ ensures \result == \dl_inDomain(map,key);
     @*/
    public /*@pure@*/ boolean containsKey(Object key);

    /*@ public normal_behaviour
    @ accessible footprint;
    @ ensures \result == (\exists Object key; \dl_inDomain(map,key); \dl_mapGet(map,key) == value);
    @*/
    public /*@pure@*/ boolean containsValue(Object value);
    
    /*@ public normal_behaviour
     @ assignable footprint;
     @ ensures \dl_mapGet(map,key) == value && \result == \old(\dl_mapGet(map,key)) &&
     @ ( \forall Object o; (\fresh(o) ==> \dl_mapGet(map,o) == null) && 
     @ (!\fresh(o) && o != key ==> \dl_mapGet(map,o) == \old(\dl_mapGet(map,o)))
     @ );
     @*/
    public /*@nullable@*/ Object put(Object key, Object value);

    /*@ public normal_behaviour
     @ assignable footprint;
     @   ensures \dl_mapGet(map,key) == null && \result == \old(\dl_mapGet(map,key)) &&
     @ ( \forall Object o; (\fresh(o) ==> \dl_mapGet(map,o) == null) && 
     @ (!\fresh(o) && o != key ==> \dl_mapGet(map,o) == \old(\dl_mapGet(map,o)))
     @ );
     @*/
    public /*@nullable@*/ Object remove(Object key);

    /*@ public normal_behaviour
     @ assignable footprint;
     @ ensures map == \dl_mapEmpty();
     @*/
    public void clear();
    
}
