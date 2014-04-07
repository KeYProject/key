package MapCaseStudy;

public interface MapInterface {

    //@ public ghost instance \locset footprint;
    //@ public ghost instance \map map;
    //@ public instance invariant \subset(\singleton(this.map), footprint);
    //@ public instance invariant \subset(\singleton(this.footprint), footprint);
    //@ public instance invariant \dl_isFinite(map);
    
    // --------
    // Method signatures and specifications
    // --------
    
    /*@ normal_behaviour
     @ ensures map == \dl_mapEmpty();
     @ assignable footprint;
     @*/
    public void clear();

    /*@ normal_behaviour
     @ ensures \result == \dl_inDomain(map, key);
     @ accessible footprint;
     @*/
    public /*@ pure @*/ boolean containsKey(Object key);

    /*@ normal_behaviour
     @ ensures \result == (\exists Object key; \dl_inDomain(map,key); \dl_mapGet(map,key) == value);
     @ accessible footprint;
     @*/
    public /*@ pure @*/ boolean containsValue(Object value);

    /*@ normal_behaviour
     @ ensures \result == (\dl_inDomain(map, key) ? \dl_mapGet(map, key) : null);
     @ accessible footprint;
     @*/
    public /*@ pure nullable @*/ Object get(Object key);

    /*@ normal_behaviour
     @ ensures \result == (map == \dl_mapEmpty());
     @ accessible footprint; 
     @*/
    public /*@ pure @*/ boolean isEmpty();

    /*@ normal_behaviour
     @ ensures map == \dl_mapUpdate(\old(map), key, value);
     @ ensures \result == (\dl_inDomain(\old(map), key) ? \dl_mapGet(\old(map), key) : null);
     @ assignable footprint;
     @*/
    public /*@ nullable @*/ Object put(Object key, Object value);

    /*@ normal_behaviour
     @ ensures map == \dl_mapRemove(\old(map), key);
     @ ensures \result == (\dl_inDomain(\old(map), key) ? \dl_mapGet(\old(map), key) : null);
     @ assignable footprint;
     @*/
    public /*@ nullable @*/ Object remove(Object key);

    /*@ normal_behaviour
     @ ensures \result == \dl_mapSize(map);
     @ accessible footprint;
     @*/
    public /*@ pure @*/ int size();

}
