package MapCaseStudy;

public abstract class AbstractMap implements MapInterface {

    public MapEntry[] entry;

    /*@
     @ public invariant (\forall int i1; 0 <= i1 && i1 < entry.length;
     @                      (\forall int i2; i1 < i2 && i2 < entry.length;
     @                          ( entry[i1].key != entry[i2].key )));
     @ public invariant \typeof(entry) == \type(MapEntry[]);
     @ public invariant entry.length == \dl_mapSize(map);
     @ public invariant (\forall int i; 0 <= i && i < entry.length;
     @                      \dl_mapGet(map, entry[i].key) == entry[i].value);
     @ public invariant (\forall Object o;
     @          (\exists int i; 0 <= i && i < entry.length; entry[i].key == o) <==> \dl_inDomain(map, o));
     @*/
    
    /*@ public invariant footprint == \set_union(\set_union(\set_union(
     @              \infinite_union(int i; 0 <= i && i < entry.length; entry[i].*), 
     @              this.*),
     @              entry.*) );
     @*/
    
    /*@ public normal_behaviour
     @ requires target != entry;
     @ requires target != null;
     @ requires 0 <= numberCopies;
     @ requires 0 <= beginTarget && beginTarget + numberCopies <= target.length;
     @ requires 0 <= beginEntry && beginEntry + numberCopies <= entry.length;
     @ requires \typeof(target) == \typeof(entry);
     @ ensures (\forall int x; 0 <= x && x < numberCopies; 
     @               ( target[beginTarget + x].key == entry[beginEntry + x].key ) &&
     @               ( target[beginTarget + x].value == entry[beginEntry + x].value ) );
     @ ensures (\forall Object o; !\fresh(o));
     @ assignable target[beginTarget..beginTarget + numberCopies - 1];
     @*/
    abstract void copyMapEntries(MapEntry[] /*@nullable*/ target,
            int beginTarget,
            int beginEntry,
            int numberCopies);
    
    /*@ public normal_behavior
     @ ensures \dl_inDomain(map, key) ? 
     @              (\result >= 0 && \result < entry.length && entry[\result].key == key) : 
     @              (\result == -1);
     @ ensures (\forall Object o; !\fresh(o));
     @ accessible footprint;
     @*/
    abstract /*@strictly_pure@*/ int getIndexOfKey(Object key);

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
    abstract /*@helper*/ /*@nullable*/ Object[] getMapEntryArray(int l);

    /*@ public normal_behaviour
     @ requires 0 <= index && index < entry.length;
     @ ensures map == \dl_mapUpdate(\old(map), entry[index].key, value);
     @ ensures \result == (\dl_mapGet(\old(map), entry[index].key));
     @ ensures (\forall Object o; !\fresh(o));
     @ assignable entry[index].value, map;
     @*/
    abstract Object putInDomain(int index, Object value);

    /*@ public normal_behaviour
     @ requires !\dl_inDomain(map, key);
     @ assignable footprint;
     @ ensures map == \dl_mapUpdate(\old(map), key, value);
     @ ensures \result == null;
     @ ensures \fresh(entry);
     @ ensures !\dl_inDomain(map, entry);
     @*/
    abstract /*nullable*/ Object putNotInDomain(Object key, Object value);

    /*@ public normal_behaviour
     @ requires entryNew != null;
     @ requires entryNew.length == entry.length - 1;
     @ requires \typeof(entryNew) == \typeof(entry);
     @ assignable entryNew[*];
     @ ensures (\forall Object o; !\fresh(o));
     @ ensures (\forall int i; 0 <= i && i < index; entryNew[i].equals(entry[i] ));
     @ ensures (\forall int i; index < i && i < entry.length; entryNew[i - 1].equals(entry[i] ));
     @*/
    abstract void removeCopy( /*nullable*/ MapEntry[] entryNew, int index);

    /*@ public normal_behaviour
     @ assignable footprint;
     @ ensures map == \dl_mapRemove(\old(map), entry[index].key);
     @ ensures \result == \dl_mapGet(\old(map), entry[index].key);
     @ ensures \fresh(entry);
     @ ensures !\dl_inDomain(map, entry);
     @*/
    abstract /*strictly_pure*/ Object removeInDomain(int index);

}
