package CaseStudyUseMaps;

final class MapImplementation implements MapInterface {

    private Object keys[];
    private Object values[];

    /*@
     @ private invariant (\forall int i1; 0 <= i1 && i1 < keys.length;
     @                   (\forall int i2; 0 <= i2 && i2 < keys.length;
     @                       (keys[i1] == keys[i2]) ==> (i1 == i2)));
     @ private invariant footprint == \set_union(\set_union(this.*,keys[*]),values[*]);
     @ private invariant \typeof(keys) == \type(Object[]);
     @ private invariant \typeof(values) == \type(Object[]);
     @ private invariant keys.length == values.length;
     @ private invariant (\forall int i; 0 <= i && i < keys.length; \dl_mapGet(map, keys[i]) == values[i]);
     @ private invariant (\forall Object o;
     @          (\exists int i; 0 <= i && i < keys.length; keys[i] == o) <==> \dl_inDomain(map, o));
     @*/
    
    //@ private invariant \dl_mapSize(map) == keys.length;
    //@ private invariant keys != values;

    /*@ normal_behaviour
     @   ensures map == \dl_mapEmpty() && \fresh(footprint);
     @*/
    public /*@pure@*/ MapImplementation() {
        keys = new Object[0];
        values = new Object[0];
        //@ set map = \dl_mapEmpty();
        //@ set footprint = \set_union(\set_union(\all_fields(keys), \all_fields(values)), \all_fields(this));
    }

    public int size() {
        return keys.length;
    }

    public Object get(Object key) {
        /*@ loop_invariant 0 <= i && i <= keys.length;
         @ loop_invariant (\forall int x; 0 <= x && x < i; key != keys[x]);
         @ decreases keys.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < keys.length; i++) {
            if (key == keys[i]) {
                return values[i];
            }
        }
        return null;
    }

    public boolean isEmpty() {
        return keys.length == 0;
    }

    public boolean containsKey(Object key) {
        /*@ loop_invariant 0 <= i && i <= keys.length;
         @ loop_invariant (\forall int x; 0 <= x && x < i; key != keys[x]);
         @ decreases keys.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < keys.length; i++) {
            if (key == keys[i]) {
                return true;
            }
        }
        return false;
    }

    public boolean containsValue(Object value) {
        /*@ loop_invariant 0 <= i && i <= keys.length
          @    && (\forall int x; x < 0 || x >= i || value != values[x]);
          @ decreases keys.length - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < keys.length; i++) {
            if (value == values[i]) {
                return true;
            }
        }
        return false;
    }
    
    /*@ private normal_behavior
     @   requires l >= 0;
     @   ensures \typeof(\result) == \type(Object[]);
     @   ensures \result.length == l;
     @   ensures \fresh(\result);
     @   ensures \result != null;
     @   ensures (\forall int i; 0 <= i && i < \result.length; \result[i] == null);
     @   ensures !\dl_inDomain(map, \result);
     @   assignable \nothing;
     @*/
    private /*@helper*/ /*@nullable*/ Object[] newArray(int l) {
        // This function is taken from ArrayList.java
        return new Object[l];
    }
    
    /*@ private normal_behavior
     @ ensures \dl_inDomain(map, key) ? 
     @           (\result >= 0 && \result < keys.length && keys[\result] == key) : 
     @           (\result == -1);
     @ ensures (\forall Object o; !\fresh(o));
     @*/
    private /*@strictly_pure@*/ int getIndexOfKey(Object key) {
        int index = -1;
        /*@ loop_invariant 0 <= i && i <= keys.length;
         @ loop_invariant ((index != -1) ==> (keys[index] == key && \dl_inDomain(map, key)));
         @ loop_invariant ((index != -1) ==> index < keys.length && index >= 0);
         @ loop_invariant ((index == -1) ==> (\forall int x; x>=0 && x<i; keys[x] != key));
         @ loop_invariant (\forall Object o; !\fresh(o));
         @ decreases keys.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < keys.length; i++) {
            if (key == keys[i]) {
                index = i;
            }
        }
        return index;
    }
    
    /*@ private normal_behaviour
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
    private void copyArray(Object[] /*@ nullable */ target,
                           Object[] source,
                           int beginTarget,
                           int beginSource,
                           int numberCopies) {
        /*@ loop_invariant 0 <= i && i <= numberCopies;
         @ loop_invariant (\forall int x; 0 <= x && x < i; 
         @ (target[beginTarget + x] == source[beginSource + x]));
         @ loop_invariant (\forall Object o; !\fresh(o));
         @ decreases numberCopies - i;
         @ assignable target[beginTarget..beginTarget + numberCopies - 1];
         @*/
        for (int i = 0; i < numberCopies; i++) {
            target[beginTarget + i] = source[beginSource + i];
        }
    }
    
    /*@ public normal_behaviour
     @ requires 0 <= index && index < keys.length;
     @ ensures map == \dl_mapUpdate(\old(map), keys[index], value);
     @ ensures \result == (\dl_mapGet(\old(map), keys[index]));
     @ ensures (\forall Object o; !\fresh(o));
     @ assignable values[index], map;
     @*/
    private Object putInDomain(int index, Object value){
        Object ret = values[index];
        values[index] = value;
        //@ set map = \dl_mapUpdate(map, keys[index], value);
        return ret;
    }
    
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
    private void putCopy(/*@nullable*/Object[] keysNew,
            /*@nullable*/ Object[] valuesNew) {
        copyArray(keysNew, keys, 0, 0, keys.length);
        copyArray(valuesNew, values, 0, 0, keys.length);
    }
    
    /*@ public normal_behaviour
     @ requires !\dl_inDomain(map, key);
     @ assignable footprint;
     @ ensures map == \dl_mapUpdate(\old(map), key, value);
     @ ensures \result == null;
     @ ensures \fresh(keys, values);
     @ ensures !\dl_inDomain(map, keys);
     @ ensures !\dl_inDomain(map, values);
     @*/
    private /*nullable*/ Object putNotInDomain(Object key, Object value) {

        Object[] keysNew = newArray(keys.length + 1);
        Object[] valuesNew = newArray(keys.length + 1);
//      Object keysNew[] = new Object[keys.length + 1];
//      Object valuesNew[] = new Object[keys.length + 1];

        putCopy(keysNew, valuesNew);

        keysNew[keys.length] = key;
        valuesNew[keys.length] = value;

        keys = keysNew;
        values = valuesNew;

        //@ set map = \dl_mapUpdate(map, key, value);
        //@ set footprint = \set_union(\set_union(\all_fields(keys), \all_fields(values)), \all_fields(this));
        return null;
    }

    public Object put(Object key, Object value) {
        int index = getIndexOfKey(key);
        if (index != -1) {
            return putInDomain(index, value);
        } else {
            return putNotInDomain(key, value);
        }
    }
    
    /*@ public normal_behaviour
     @ requires keysNew != valuesNew;
     @ requires valuesNew != null;
     @ requires keysNew != null;
     @ requires keysNew.length == keys.length - 1;
     @ requires valuesNew.length == values.length - 1;
     @ requires \typeof(keysNew) == \typeof(keys);
     @ requires \typeof(valuesNew) == \typeof(values);
     @ assignable keysNew[0..index - 1], valuesNew[0..index - 1];
     @ ensures (\forall Object o; !\fresh(o));
     @ ensures (\forall int i; 0 <= i && i < index;
     @                  keysNew[i] == keys[i] && valuesNew[i] == values[i]);
     @*/
    private void removeCopyLower(/*nullable*/Object[] keysNew, /*nullable*/ Object[] valuesNew, int index) {
        copyArray(keysNew, keys, index, 0, 0);
        copyArray(valuesNew, values, index, 0, 0);
    }
    
    /*@ public normal_behaviour
     @ requires keysNew != valuesNew;
     @ requires valuesNew != null;
     @ requires keysNew != null;
     @ requires keysNew.length == keys.length - 1;
     @ requires valuesNew.length == values.length - 1;
     @ requires \typeof(keysNew) == \typeof(keys);
     @ requires \typeof(valuesNew) == \typeof(values);
     @ assignable keysNew[index..keys.length - 1], valuesNew[index..values.length - 1];
     @ ensures (\forall Object o; !\fresh(o));
     @ ensures (\forall int i; index < i && i < keys.length;
     @                  keysNew[i - 1] == keys[i] && valuesNew[i - 1] == values[i]);
     @*/
    private void removeCopyUpper(/*nullable*/Object[] keysNew, /*nullable*/ Object[] valuesNew, int index) {
        copyArray(keysNew, keys, keys.length - (index + 1), index, index + 1);
        copyArray(keysNew, keys, keys.length - (index + 1), index, index + 1);
    }
    
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
    private void removeCopy(/*nullable*/Object[] keysNew, /*nullable*/ Object[] valuesNew, int index) {
        removeCopyLower(keysNew, valuesNew, index);
        removeCopyUpper(keysNew, valuesNew, index);
    }
    
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
    private Object removeInDomain(Object key, int index) {

        Object ret = values[index];

        Object keysNew[] = newArray(keys.length - 1);
        Object valuesNew[] = newArray(keys.length - 1);
        
        removeCopy(keysNew, valuesNew, index);

        keys = keysNew;
        values = valuesNew;

        //@ set map = \dl_mapRemove(map, key);
        //@ set footprint = \set_union(\set_union(\all_fields(keys), \all_fields(values)), \all_fields(this));
        return ret;
    }

    public Object remove(Object key) {

        int index = getIndexOfKey(key);

        if (index == -1) {
            return null;
        } else {
            return removeInDomain(key, index);
        }
    }

    public void clear() {
        keys = new Object[0];
        values = new Object[0];
        //@ set map = \dl_mapEmpty();
        //@ set footprint = \set_union(\set_union(\all_fields(keys), \all_fields(values)), \all_fields(this));
    }

}
