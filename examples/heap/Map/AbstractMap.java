package MapCaseStudy;

public abstract class AbstractMap implements MapInterface {

    public Object keys[];
    public Object values[];

    /*@
     @ public invariant (\forall int i1; 0 <= i1 && i1 < keys.length;
     @                   (\forall int i2; 0 <= i2 && i2 < keys.length;
     @                       (keys[i1] == keys[i2]) ==> (i1 == i2)));
     @ public invariant footprint == \set_union(\set_union(this.*,keys[*]),values[*]);
     @ public invariant \typeof(keys) == \type(Object[]);
     @ public invariant \typeof(values) == \type(Object[]);
     @ public invariant keys.length == values.length;
     @ public invariant (\forall int i; 0 <= i && i < keys.length; \dl_mapGet(map, keys[i]) == values[i]);
     @ public invariant (\forall Object o;
     @          (\exists int i; 0 <= i && i < keys.length; keys[i] == o) <==> \dl_inDomain(map, o));
     @*/
    //@ public invariant \dl_mapSize(map) == keys.length;
    //@ public invariant keys != values;

    /*@ public normal_behavior
     @   requires l >= 0;
     @   ensures \typeof(\result) == \type(Object[]);
     @   ensures \result.length == l;
     @   ensures \fresh(\result);
     @   ensures \result != null;
     @   ensures (\forall int i; 0 <= i && i < \result.length; \result[i] == null);
     @   ensures !\dl_inDomain(map, \result);
     @   assignable \nothing;
     @*/
    abstract /*@helper*/ /*@nullable*/ Object[] newArray(int l);

    /*@ public normal_behavior
     @ ensures \dl_inDomain(map, key) ? 
     @           (\result >= 0 && \result < keys.length && keys[\result] == key) : 
     @           (\result == -1);
     @ ensures (\forall Object o; !\fresh(o));
     @*/
    abstract /*@strictly_pure@*/ int getIndexOfKey(Object key);

    /*@ public normal_behaviour
     @ requires target != source;
     @ requires target != keys;
     @ requires target != values;
     @ requires target != null;
     @ requires 0 <= numberCopies;
     @ requires 0 <= beginTarget && beginTarget + numberCopies <= target.length;
     @ requires 0 <= beginSource && beginSource + numberCopies <= source.length;
     @ requires \typeof(target) == \typeof(source);
     @ ensures (\forall int index; 0 <= index && index < numberCopies;
     @                         target[beginTarget + index] == source[beginSource + index]);
     @ ensures (\forall Object o; !\fresh(o));
     @ assignable target[beginTarget..beginTarget + numberCopies - 1];
     @*/
    abstract void copyArray(Object[] /*@nullable*/ target,
            Object[] source,
            int beginTarget,
            int beginSource,
            int numberCopies);

    /*@ public normal_behaviour
     @ requires 0 <= index && index < keys.length;
     @ ensures map == \dl_mapUpdate(\old(map), keys[index], value);
     @ ensures \result == (\dl_mapGet(\old(map), keys[index]));
     @ ensures (\forall Object o; !\fresh(o));
     @ assignable values[index], map;
     @*/
    abstract Object putInDomain(int index, Object value);

    /*@ public normal_behaviour
     @ requires keysNew != valuesNew;
     @ requires valuesNew != null;
     @ requires keysNew != null;
     @ requires keysNew.length == keys.length + 1;
     @ requires valuesNew.length == values.length + 1;
     @ requires \typeof(keysNew) == \typeof(keys);
     @ requires \typeof(valuesNew) == \typeof(values);
     @ assignable keysNew[0..keys.length - 1], valuesNew[0..values.length - 1];
     @ ensures (\forall Object o; !\fresh(o));
     @ ensures (\forall int i; 0<=i && i<keys.length;
     @                   keysNew[i] == keys[i] && valuesNew[i] == values[i]);
     @*/
    abstract void putCopy(/*@nullable*/Object[] keysNew,
            /*@nullable*/ Object[] valuesNew);

    /*@ public normal_behaviour
     @ requires !\dl_inDomain(map, key);
     @ assignable footprint;
     @ ensures map == \dl_mapUpdate(\old(map), key, value);
     @ ensures \result == null;
     @ ensures \fresh(keys, values);
     @ ensures !\dl_inDomain(map, keys);
     @ ensures !\dl_inDomain(map, values);
     @*/
    abstract /*nullable*/ Object putNotInDomain(Object key, Object value);

    /*@ public normal_behaviour
     @ requires keysNew != valuesNew;
     @ requires valuesNew != null;
     @ requires keysNew != null;
     @ requires keysNew.length == keys.length - 1;
     @ requires valuesNew.length == values.length - 1;
     @ requires \typeof(keysNew) == \typeof(keys);
     @ requires \typeof(valuesNew) == \typeof(values);
     @ assignable keysNew[*], valuesNew[*];
     @ ensures (\forall Object o; !\fresh(o));
     @ ensures (\forall int i; 0 <= i && i < index;
     @                  keysNew[i] == keys[i] && valuesNew[i] == values[i]);
     @ ensures (\forall int i; index < i && i < keys.length;
     @                  keysNew[i - 1] == keys[i] && valuesNew[i - 1] == values[i]);
     @*/
    abstract void removeCopy(/*nullable*/Object[] keysNew, /*nullable*/ Object[] valuesNew, int index);

    /*@ public normal_behaviour
     @ requires \dl_inDomain(map, key);
     @ requires keys[index] == key;
     @ assignable footprint;
     @ ensures map == \dl_mapRemove(\old(map), key);
     @ ensures \result == \dl_mapGet(\old(map), key);
     @ ensures \fresh(keys, values);
     @ ensures !\dl_inDomain(map, keys);
     @ ensures !\dl_inDomain(map, values);
     @*/
    abstract Object removeInDomain(Object key, int index);

}
