package CaseStudyUseMaps;

final class MapImplementation implements Map2 {

    private Object keys[];
    private Object values[];

    /*@
     @ private invariant (\forall int i1; 0 <= i1 && i1 <= keys.length;
     @                   (\forall int i2; 0 <= i2 && i2 <= keys.length && i1 != i2; keys[i1] != keys[i2]));
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
     @ private invariant (keys.length == 0) <==> (map == \dl_mapEmpty());
     @*/

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

    public Object get(Object o) {
        /*@ loop_invariant 0 <= i && i <= keys.length;
         @ loop_invariant (\forall int x; 0 <= x && x < i; o != keys[x]);
         @ decreases keys.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < keys.length; i++) {
            if (o == keys[i]) {
                return values[i];
            }
        }
        return null;
    }

    public boolean isEmpty() {
        return keys.length == 0;
    }

    public Object put(Object k, Object v) {
        Object old = get(k);
        if (!containsKey(k)) {
            Object keysNew[] = new Object[keys.length + 1];
            Object valuesNew[] = new Object[keys.length + 1];
            for (int i = 0; i < keys.length; i++) {
                keysNew[i] = keys[i];
                valuesNew[i] = values[i];
            }
            keysNew[keys.length] = k;
            valuesNew[keys.length] = v;

            keys = keysNew;
            values = valuesNew;
        } else {
            for (int i = 0; i < keys.length; i++) {
                if (keys[i] == k) {
                    values[i] = v;
                }
            }
        }
        return old;
    }

    public boolean containsKey(Object o) {
        /*@ loop_invariant 0 <= i && i <= keys.length;
         @  loop_invariant (\forall int x; 0 <= x && x < i; o != keys[x]);
         @ decreases keys.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < keys.length; i++) {
            if (o == keys[i]) {
                return true;
            }
        }
        return false;
    }

    public boolean containsValue(Object o) {
        /*@ loop_invariant 0 <= i && i <= keys.length
          @    && (\forall int x; x < 0 || x >= i || o != values[x]);
          @ decreases keys.length - i;
          @ assignable \strictly_nothing;
          @*/
        for (int i = 0; i < keys.length; i++) {
            if (o == values[i]) {
                return true;
            }
        }
        return false;
    }

    public Object remove(Object key) {

        int index = -1;
        int i;

         /*@ loop_invariant 0 <= i && i <= keys.length;
         @ loop_invariant (\forall int x; 0 <= x && x < i; key != keys[x]);
         @ decreases keys.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (i = 0; i < keys.length; i++) {
            if (key == keys[i]) {
                index = i;
            }
        }
        
        if(index == -1){
            return null;
        }

        Object ret = values[index];
        Object keysNew[] = new Object[keys.length - 1];
        Object valuesNew[] = new Object[keys.length - 1];

        /*@ loop_invariant 0 <= i && i <= keys.length;
         @ loop_invariant (\forall int x; 0 <= x && x < i;
         @ ( (x < index) ==> ( keysNew[x] == keys[x] && valuesNew[x] == values[x] )) && 
         @ ( (x > index) ==> ( keysNew[x] == keys[x - 1] && valuesNew[x] == values[x - 1] ))
         @ );
         @ decreases keys.length - i;
         @ assignable footprint;
         @*/
        for (i = 0; i < keys.length; i++) {
            if (i < index) {
                keysNew[i] = keys[i];
                valuesNew[i] = values[i];
            }
            if (i > index) {
                keysNew[i] = keys[i - 1];
                valuesNew[i] = values[i - 1];
            }
        }

        keys = keysNew;
        values = valuesNew;
        
        //@ set map = \dl_mapRemove(map, key);
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
