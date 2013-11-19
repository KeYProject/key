package MapCaseStudy;

final class AMapImplementation extends AbstractMap {

    /*@ normal_behaviour
     @ ensures map == \dl_mapEmpty();
     @*/
    public /*@pure@*/ AMapImplementation() {
        entry = new MapEntry[0];
        //@ set map = \dl_mapEmpty();
        //@ set footprint = \set_union(\all_fields(this), \all_fields(entry));
    }
    
    public void clear() {
        entry = new MapEntry[0];
        //@ set map = \dl_mapEmpty();
        //@ set footprint = \set_union(\all_fields(this), \all_fields(entry));
    }
    
    public boolean containsKey(Object key) {
        return getIndexOfKey(key) != -1;
    }

    public boolean containsValue(Object value) {
        /*@ loop_invariant 0 <= i && i <= entry.length;
         @ loop_invariant (\forall int x; 0 <= x && x < i; value != entry[x].value);
         @ decreases entry.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < entry.length; i++) {
            if (value == entry[i].value) {
                return true;
            }
        }
        return false;
    }
    
    void copyMapEntries(MapEntry[] target,
            int beginTarget,
            int beginEntry,
            int numberCopies) {
        /*@ loop_invariant 0 <= i && i <= numberCopies;
         @ loop_invariant (\forall int x; 0 <= x && x < i; 
         @               ( target[beginTarget + x] == entry[beginEntry + x] ));
         @ loop_invariant (\forall Object o; !\fresh(o));
         @ decreases numberCopies - i;
         @ assignable target[beginTarget..beginTarget + numberCopies - 1];
         @*/
        for (int i = 0; i < numberCopies; i++) {
            target[beginTarget + i] = entry[beginEntry + i];
        }
    }

    public Object get(Object key) {
        int index = getIndexOfKey(key);
        if (index == -1) {
            return null;
        } else {
            return entry[index].value;
        }
    }

    int getIndexOfKey(Object key) {
        /*@ loop_invariant 0 <= i && i <= entry.length;
         @ loop_invariant (\forall int x; x>=0 && x<i; entry[x].key != key);
         @ loop_invariant (\forall Object o; !\fresh(o));
         @ decreases entry.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < entry.length; i++) {
            if (key == entry[i].key) {
                return i;
            }
        }
        return -1;
    }

    MapEntry[] getMapEntryArray(int l) {
        // This function is modeled after ArrayList.newArray()
        return new MapEntry[l];
    }

    public boolean isEmpty() {
        return entry.length == 0;
    }

    public Object put(Object key, Object value) {
        int index = getIndexOfKey(key);
        if (index == -1) {
            return putNotInDomain(key, value);
        } else {
            return putInDomain(index, value);
        }
    }
    
   MapEntry putCreateMapEntry(Object key, Object value){
       return new MapEntry(key, value);
   }
   
   MapEntry[] putExtendArray(Object key, Object value) {
        MapEntry[] result = getMapEntryArray(entry.length + 1);
        copyMapEntries(result, 0, 0, entry.length);
        result[entry.length] = putCreateMapEntry(key, value);
        return result;
    }

    Object putInDomain(int index, Object value) {
        Object result = entry[index].value;
        entry[index].value = value;
        //@ set map = \dl_mapUpdate(map, entry[index].key, value);
        return result;
    }

    Object putNotInDomain(Object key, Object value) {
        MapEntry[] newEntry = putExtendArray(key, value);
        entry = newEntry;
        //@ set footprint = \set_union(\dl_allElementsOfArray(entry, \all_fields(entry[0])), \set_union(\all_fields(this), \all_fields(entry)));
        //@ set map = \dl_mapUpdate(map, key, value);
        return null;
    }
    
    public Object remove(Object key) {
        int index = getIndexOfKey(key);
        if (index == -1) {
            return null;
        } else {
            return removeInDomain(index);
        }
    }
    
    /*@ public normal_behaviour
     @ requires entryNew != null;
     @ requires entryNew != entry;
     @ requires entry.length > 0;
     @ requires entryNew.length == entry.length - 1;
     @ requires \typeof(entryNew) == \typeof(entry);
     @ requires 0 < index && index < entry.length;
     @ ensures (\forall Object o; !\fresh(o));
     @ ensures (\forall int i; 0 <= i && i < index;
     @               entryNew[i] == entry[i]);
     @ assignable entryNew[0..index - 1];
     @*/
    void c1( /*@nullable*/MapEntry[] entryNew, int index) {
            copyMapEntries(entryNew, 0, 0, index);
    }
    
    /*@ public normal_behaviour
     @ requires entryNew != null;
     @ requires entryNew != entry;
     @ requires entry.length > 0;
     @ requires entryNew.length == entry.length - 1;
     @ requires \typeof(entryNew) == \typeof(entry);
     @ requires 0 <= index && index < entryNew.length;
     @ ensures (\forall Object o; !\fresh(o));
     @ ensures (\forall int i;  index <= i && i < entryNew.length;
     @               entryNew[i] == entry[i + 1]);
     @ assignable entryNew[index..entryNew.length - 1];
     @*/
    void c2( /*@nullable*/MapEntry[] entryNew, int index) {
            copyMapEntries(entryNew, index, index + 1, entryNew.length - index);
    }

    void removeCopy(MapEntry[] entryNew, int index) {
        if (index > 0) {
            c1(entryNew, index);
        }
        if (index < entryNew.length) {
            c2(entryNew, index);
        }
    }

    Object removeInDomain(int index) {
        Object result = entry[index].value;
        MapEntry[] entryNew = getMapEntryArray(entry.length - 1);
        removeCopy(entryNew, index);
        entry = entryNew;
        //@ set map = \dl_mapRemove(map, entry[index].key);
        //@ set footprint = \set_union(\dl_allElementsOfArray(entry, \all_fields(entry[0])), \set_union(\all_fields(this), \all_fields(entry)));
        return result;
    }
    
    public int size() {
        return entry.length;
    }

}
