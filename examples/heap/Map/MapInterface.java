package MapCaseStudy;

public interface MapInterface {
    
    //@ public ghost instance \locset footprint;
    //@ public ghost instance \free map;
    
    //@ public instance invariant \subset(\singleton(this.map), footprint);
    //@ public instance invariant \subset(\singleton(this.footprint), footprint);
    
    //@ public instance invariant \dl_isFinite(map);
    
    // -----
    // Method signatures + specs
    // -----
    
    /*@ public normal_behaviour
     @ assignable footprint;
     @ ensures map == \dl_mapEmpty();
     @*/
    public void clear();
    
    /*@ public normal_behaviour
     @ accessible footprint;
     @ ensures \result == \dl_inDomain(map, key);
     @*/
    public /*@pure@*/ boolean containsKey(Object key);

    /*@ public normal_behaviour
    @ accessible footprint;
    @ ensures \result == (\exists Object key; \dl_inDomain(map,key); \dl_mapGet(map,key) == value);
    @*/
    public /*@pure@*/ boolean containsValue(Object value);
    
    /*@ public normal_behaviour
    @ accessible footprint;
    @ ensures \result == (\dl_inDomain(map, key) ? \dl_mapGet(map, key) : null);
    @*/
    public /*@pure nullable@*/ Object get(Object key);

    /*@ public normal_behaviour
     @ accessible footprint;
     @ ensures \result == (map == \dl_mapEmpty());
     @*/
    public /*@pure@*/ boolean isEmpty();
    
    /*@ public normal_behaviour
     @ assignable footprint;
     @ ensures map == \dl_mapUpdate(\old(map), key, value);
     @ ensures \result == (\dl_inDomain(\old(map), key) ? \dl_mapGet(\old(map), key) : null);
     @*/
    public /*@nullable@*/ Object put(Object key, Object value);

    /* What if size() == 1 before remove? 
     * Do I have to set map = mapEmpty in case inDomain(map, key)?
     */
    
    /*@ public normal_behaviour
     @ assignable footprint;
     @ ensures map == \dl_mapRemove(map, key);
     @ ensures \result == (\dl_inDomain(\old(map), key) ? \dl_mapGet(\old(map), key) : null);
     @*/
    public /*@nullable@*/ Object remove(Object key);
    
    /*@ public normal_behaviour
     @ accessible footprint;
     @ ensures \result == \dl_mapSize(map);
     @*/
    public /*@pure@*/ int size();
    
}
