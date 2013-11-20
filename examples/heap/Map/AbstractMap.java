package MapCaseStudy;

public abstract class AbstractMap implements MapInterface {

    public MapEntry[] entries;

    /*@
     @ public invariant (\forall int i1; 0 <= i1 && i1 < entries.length;
     @                      (\forall int i2; i1 < i2 && i2 < entries.length;
     @                          ( entries[i1].key != entries[i2].key )));
     @ public invariant \typeof(entries) == \type(MapEntry[]);
     @ public invariant entries.length == \dl_mapSize(map);
     @ public invariant (\forall int i; 0 <= i && i < entries.length;
     @                      \dl_mapGet(map, entries[i].key) == entries[i].value);
     @ public invariant (\forall Object o;
     @          (\exists int i; 0 <= i && i < entries.length; entries[i].key == o) <==> \dl_inDomain(map, o));
     @*/
    
    /*@ public invariant (\forall int i; 0 <= i && i < entries.length; 
      @          entries[i] != null && entries[i].key != null && entries[i].value != null); */
    
    /*@ public invariant footprint ==
     @      \set_union(\infinite_union(int i; 0 <= i && i < entries.length; entries[i].*),
     @                 this.*,
     @                 entries.*);
     @*/
    
    /*@ public normal_behaviour
     @ requires target != entries;
     @ requires target != null;
     @ requires 0 <= numberCopies;
     @ requires 0 <= targetIndex && targetIndex + numberCopies <= target.length;
     @ requires 0 <= entriesIndex && entriesIndex + numberCopies <= entries.length;
     @ requires \typeof(target) == \typeof(entries);
     @ ensures (\forall int x; 0 <= x && x < numberCopies; 
     @               ( target[targetIndex + x] == entries[entriesIndex + x]));
     @ ensures (\forall Object o; !\fresh(o));
     @ assignable target[targetIndex..targetIndex + numberCopies - 1];
     @*/
    abstract void copyMapEntries(MapEntry[] /*@nullable*/ target,
            int targetIndex,
            int entriesIndex,
            int numberCopies);
    
    /*@ public normal_behavior
     @ ensures \dl_inDomain(map, key) ? 
     @              (\result >= 0 && \result < entries.length && entries[\result].key == key) : 
     @              (\result == -1);
     @ ensures (\forall Object o; !\fresh(o));
     @ accessible footprint;
     @*/
    abstract /*@strictly_pure@*/ int getIndexOfKey(Object key);
    
    /*@ public normal_behavior
     @   ensures \fresh(\result);
     @   ensures \result.key == key;
     @   ensures \result.value == value;
     @   ensures !\dl_inDomain(map, \result);
     @   assignable \nothing;
     @*/
    abstract MapEntry newMapEntry(Object key, Object value);

    /*@ public normal_behavior
     @   requires l >= 0;
     @   ensures \typeof(\result) == \type(MapEntry[]);
     @   ensures \result.length == l;
     @   ensures \fresh(\result);
     @   ensures \result != null;
     @   ensures (\forall int i; 0 <= i && i < \result.length; \result[i] == null);
     @   ensures !\dl_inDomain(map, \result);
     @   assignable \nothing;
     @*/
    abstract /*@helper nullable*/ MapEntry[] newMapEntryArray(int l);
    
    /*@ public normal_behaviour
     @ ensures \result.length == entries.length + 1;
     @ ensures (\forall int i; 0 <= i && i < entries.length; \result[i] == entries[i]);
     @ ensures \result[entries.length].key == key;
     @ ensures \result[entries.length].value == value;
     @ ensures \fresh(\result, \result[entries.length]);
     @ ensures \typeof(\result) == \type(MapEntry[]);
     @*/
    abstract /*@ pure */ MapEntry[] putExtendArray(Object key, Object value);

    /*@ public normal_behaviour
     @ requires 0 <= index && index < entries.length;
     @ ensures map == \dl_mapUpdate(\old(map), entries[index].key, value);
     @ ensures \result == (\dl_mapGet(\old(map), entries[index].key));
     @ ensures (\forall Object o; !\fresh(o));
     @ assignable entries[index].value, map;
     @*/
    abstract Object putInDomain(int index, Object value);

    /*@ public normal_behaviour
     @ requires !\dl_inDomain(map, key);
     @ assignable footprint;
     @ ensures map == \dl_mapUpdate(\old(map), key, value);
     @ ensures \result == null;
     @ ensures \fresh(entries, entries[entries.length - 1]);
     @ ensures !\dl_inDomain(map, entries);
     @ ensures !\dl_inDomain(map, entries[entries.length - 1]);
     @*/
    abstract /*@ nullable */ Object putNotInDomain(Object key, Object value);

    /*@ public normal_behaviour
     @ requires newEntries != null;
     @ requires newEntries != entries;
     @ requires entries.length > 0;
     @ requires newEntries.length == entries.length - 1;
     @ requires \typeof(newEntries) == \typeof(entries);
     @ requires 0 <= index && index < entries.length;
     @ ensures (\forall Object o; !\fresh(o));
     @ ensures (\forall int i; 0 <= i && i < newEntries.length;
     @               newEntries[i] == ((i < index) ? entries[i] : entries[i + 1]));
     @ assignable newEntries[*];
     @*/
    abstract void removeCopyOldEntries( /*@nullable*/ MapEntry[] newEntries, int index);

    /*@ public normal_behaviour
     @ requires 0 <= index && index < entries.length;
     @ ensures map == \dl_mapRemove(\old(map), entries[index].key);
     @ ensures \result == \dl_mapGet(\old(map), entries[index].key);
     @ ensures \fresh(entries);
     @ ensures !\dl_inDomain(map, entries);
     @ assignable footprint;
     @*/
    abstract Object removeInDomain(int index);

}
