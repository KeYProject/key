package CaseStudyUseMaps;

final class MapImplementation implements Map2 {

    private Object keys[];
    private Object values[];

    /*@
     @ private invariant (\forall int i1; 0 <= i1 && i1 < keys.length;
     @                   (\forall int i2; 0 <= i2 && i2 < keys.length;
                            (keys[i1] == keys[i2]) ==> (i1 == i2)));
     @ private invariant keys != null;
     @ private invariant values != null;
     @ private invariant footprint == \set_union(\set_union(this.*,keys[*]),values[*]);
     @ private invariant (\forall int i; 0 <= i && i < keys.length; keys[i] != null);
     @ private invariant (\forall int i; 0 <= i && i < keys.length; values[i] != null);
     @ private invariant \typeof(keys) == \type(Object[]);
     @ private invariant \typeof(values) == \type(Object[]);
     @ private invariant keys.length == values.length;
     @ private invariant (\forall int i; i < 0 || i >= keys.length || \dl_mapGet(map, keys[i]) == values[i]);
     @ private invariant (\forall Object o;
     @ (\exists int i; i >= 0 && i < keys.length && keys[i] == o) <==> \dl_inDomain(map, o));
     @*/
    
    //@ private invariant \dl_mapSize(map) == keys.length;
    //@ private invariant (\forall int i; i>=0 && i<keys.length; \dl_inDomain(map, keys[i]));

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
         @  loop_invariant (\forall int x; 0 <= x && x < i; key != keys[x]);
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
     @ ensures (\forall int j; j >= 0 && j < keys.length; 
     @           (j != \result <==> keys[j] != key ));
     @*/
    private /*@strictly_pure@*/ int getIndexOfKey(Object key) {
        int index = -1;
        /*@ loop_invariant 0 <= i && i <= keys.length;
         @ loop_invariant ((index != -1) ==> (keys[index] == key && \dl_inDomain(map, key)));
         @ loop_invariant ((index != -1) ==> index < keys.length && index >= 0);
         @ loop_invariant ((index == -1) ==> (\forall int x; x>=0 && x<i; keys[x] != key));
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
    
    public Object put(Object key, Object value) {
        
        int index = getIndexOfKey(key);
        Object ret = null;
        
        if (index != -1) {
            ret = values[index];
            values[index] = value;
        }
        else {

            Object keysNew[] = newArray(keys.length + 1);
            Object valuesNew[] = newArray(keys.length + 1);
            
            /*@ loop_invariant 0 <= i && i <= keys.length;
             @ loop_invariant (\forall int x; 0 <= x && x < i; 
             @ (keysNew[x] == keys[x] && valuesNew[x] == values[x]));
             @ decreases keys.length - i;
             @ assignable \set_union(keysNew[*], valuesNew[*]);
             @*/
            for (int i = 0; i < keys.length; i++) {
                keysNew[i] = keys[i];
                valuesNew[i] = values[i];
            }
            keysNew[keys.length] = key;
            valuesNew[keys.length] = value;

            keys = keysNew;
            values = valuesNew;

        }
        
        //@ set map = \dl_mapUpdate(map, key, value);
        //@ set footprint = \set_union(\set_union(\all_fields(keys), \all_fields(values)), \all_fields(this));
        return ret;
    }

    public Object remove(Object key) {

        int index = getIndexOfKey(key);
        Object ret = null;

        if (index != -1) {
            
            ret = values[index];

            Object keysNew[] = newArray(keys.length - 1);
            Object valuesNew[] = newArray(keys.length - 1);
            
            int i;

            /*@ loop_invariant 0 <= i && i <= index && index < keys.length;
             @ loop_invariant (\forall int x; 0 <= x && x < i;
             @ (keysNew[x] == keys[x] && valuesNew[x] == values[x]));
             @ decreases keys.length - i;
             @ assignable \set_union(keysNew[*], valuesNew[*]);
             @*/
            for (i = 0; i < index; i++) {
                    keysNew[i] = keys[i];
                    valuesNew[i] = values[i];
            }
            
            /*@ loop_invariant index + 1 <= i && i <= keys.length && index < keys.length;
             @ loop_invariant (\forall int x; index + 1 <= x && x < i;
             @ (keysNew[x] == keys[x - 1] && valuesNew[x] == values[x - 1]));
             @ decreases keys.length - i;
             @ assignable \set_union(keysNew[*], valuesNew[*]);
             @*/
            for (i = index + 1; i < keys.length; i++) {
                keysNew[i] = keys[i - 1];
                valuesNew[i] = values[i - 1];
            }

            keys = keysNew;
            values = valuesNew;

        }

        //@ set map = (keys.length > 0) ? \dl_mapRemove(map, key) : \dl_mapEmpty();
        //@ set footprint = \set_union(\set_union(\all_fields(keys), \all_fields(values)), \all_fields(this));
        return ret;
    }

    public void clear() {
        keys = new Object[0];
        values = new Object[0];
        //@ set map = \dl_mapEmpty();
        //@ set footprint = \set_union(\set_union(\all_fields(keys), \all_fields(values)), \all_fields(this));
    }

}
