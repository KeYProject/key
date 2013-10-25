package CaseStudyUseMaps;

public interface Map2 {
    
    //@ public ghost instance \locset footprint;
    //@ public ghost instance \free map;
    
    //@ public instance invariant \subset(\singleton(this.map), footprint);
    //@ public instance invariant \subset(\singleton(this.footprint), footprint);
    
    // @ public instance invariant \dl_isFinite(map);
    // @ private invariant \dl_mapSize(map) == keys.length;
    
    // -----
    // Method signatures + specs
    // -----
    
    /*@ public normal_behaviour
    @ accessible footprint;
    @ ensures \result == (\dl_inDomain(map, key)?\dl_mapGet(map, key):null);
    @*/
    public /*@pure nullable@*/ Object get(Object key);

    /*@ public normal_behaviour
     @ accessible footprint;
     @ ensures \result == (map == \dl_mapEmpty());
     @*/
    public /*@pure@*/ boolean isEmpty();
    
    /*@ public normal_behaviour
     @ accessible footprint;
     @ ensures \result == (\sum Object key; \dl_inDomain(map,key); 1);
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
     @ ensures \dl_mapGet(map,key) == value &&
     @ \dl_inDomain(map, key) &&
     @ \result == \old((\dl_inDomain(map, key)?\dl_mapGet(map, key):null)) &&
     @ (\forall Object o; (\fresh(o) ==> !\dl_inDomain(map,o)) &&
     @ (!\fresh(o) && o != key ==> \dl_mapGet(map,o) == \old(\dl_mapGet(map,o)))
     @ );
     @*/
    public /*@nullable@*/ Object put(Object key, Object value);

    /* What if keys.length == 1 before remove? 
     * Do I have to set map = mapEmpty in that case?
     */
    
    /*@ public normal_behaviour
     @ assignable footprint;
     @ ensures !\dl_inDomain(map,key) &&
     @ \result == \old((\dl_inDomain(map, key)?\dl_mapGet(map, key):null)) &&
     @ (\forall Object o; (\fresh(o) ==> !\dl_inDomain(map,o)) &&
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
