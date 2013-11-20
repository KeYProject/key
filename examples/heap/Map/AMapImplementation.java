package MapCaseStudy;

final class AMapImplementation extends AbstractMap {

    /*@ normal_behaviour
     @ ensures map == \dl_mapEmpty();
     @*/
    public /*@pure@*/ AMapImplementation() {
        entries = new MapEntry[0];
        //@ set map = \dl_mapEmpty();
        //@ set footprint = \set_union(\all_fields(this), \all_fields(entries));
    }
    
    public void clear() {
        entries = new MapEntry[0];
        //@ set map = \dl_mapEmpty();
        //@ set footprint = \set_union(\all_fields(this), \all_fields(entries));
    }
    
    public boolean containsKey(Object key) {
        return getIndexOfKey(key) != -1;
    }

    public boolean containsValue(Object value) {
        /*@ loop_invariant 0 <= i && i <= entries.length;
         @ loop_invariant (\forall int x; 0 <= x && x < i; value != entries[x].value);
         @ decreases entries.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < entries.length; i++) {
            if (value == entries[i].value) {
                return true;
            }
        }
        return false;
    }
    
    void copyMapEntries(MapEntry[] target,
            int targetIndex,
            int entriesIndex,
            int numberCopies) {
        /*@ loop_invariant 0 <= i && i <= numberCopies;
         @ loop_invariant (\forall int x; 0 <= x && x < i; 
         @               ( target[targetIndex + x] == entries[entriesIndex + x] ));
         @ loop_invariant (\forall Object o; !\fresh(o));
         @ decreases numberCopies - i;
         @ assignable target[targetIndex..targetIndex + numberCopies - 1];
         @*/
        for (int i = 0; i < numberCopies; i++) {
            target[targetIndex + i] = entries[entriesIndex + i];
        }
    }

    public Object get(Object key) {
        int index = getIndexOfKey(key);
        if (index == -1) {
            return null;
        } else {
            return entries[index].value;
        }
    }

    int getIndexOfKey(Object key) {
        /*@ loop_invariant 0 <= i && i <= entries.length;
         @ loop_invariant (\forall int x; x>=0 && x<i; entries[x].key != key);
         @ loop_invariant (\forall Object o; !\fresh(o));
         @ decreases entries.length - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < entries.length; i++) {
            if (key == entries[i].key) {
                return i;
            }
        }
        return -1;
    }

    public boolean isEmpty() {
        return entries.length == 0;
    }
    
    MapEntry newMapEntry(Object key, Object value) {
        return new MapEntry(key, value);
    }

    MapEntry[] newMapEntryArray(int l) {
        // This function is modeled after ArrayList.newArray()
        return new MapEntry[l];
    }

    public Object put(Object key, Object value) {
        int index = getIndexOfKey(key);
        if (index == -1) {
            return putNotInDomain(key, value);
        } else {
            return putInDomain(index, value);
        }
    }
   
   MapEntry[] putExtendArray(Object key, Object value) {
        MapEntry[] result = newMapEntryArray(entries.length + 1);
        copyMapEntries(result, 0, 0, entries.length);
        result[entries.length] = newMapEntry(key, value);
        return result;
    }

    Object putInDomain(int index, Object value) {
        Object result = entries[index].value;
        entries[index].value = value;
        //@ set map = \dl_mapUpdate(map, entries[index].key, value);
        return result;
    }

    Object putNotInDomain(Object key, Object value) {
        MapEntry[] newEntry = putExtendArray(key, value);
        entries = newEntry;
        //@ set footprint = \set_union(\dl_allElementsOfArray(entries, \all_fields(entries[0])), \set_union(\all_fields(this), \all_fields(entries)));
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
    
    void removeCopy(MapEntry[] entriesNew, int index) {
        copyMapEntries(entriesNew, 0, 0, index);
        copyMapEntries(entriesNew, index, index + 1, entriesNew.length - index);
    }

    Object removeInDomain(int index) {
        Object result = entries[index].value;
        MapEntry[] entriesNew = newMapEntryArray(entries.length - 1);
        removeCopy(entriesNew, index);
        entries = entriesNew;
        //@ set map = \dl_mapRemove(map, entries[index].key);
        //@ set footprint = \set_union(\dl_allElementsOfArray(entries, \all_fields(entries[0])), \set_union(\all_fields(this), \all_fields(entries)));
        return result;
    }
    
    public int size() {
        return entries.length;
    }

}
