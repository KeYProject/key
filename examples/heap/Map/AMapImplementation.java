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
         @               ( target[beginTarget + x].key == entry[beginEntry + x].key ) &&
         @               ( target[beginTarget + x].value == entry[beginEntry + x].value ) );
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
        if (index != -1) {
            return entry[index].value;
        } else {
            return null;
        }
    }

    public boolean isEmpty() {
        return entry.length == 0;
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

    Object putInDomain(int index, Object value) {
        Object ret = entry[index].value;
        entry[index].value = value;
        //@ set map = \dl_mapUpdate(map, entry[index].key, value);
        return ret;
    }

    Object putNotInDomain(Object key, Object value) {
        MapEntry[] entryNew = getMapEntryArray(entry.length + 1);
        copyMapEntries(entryNew, 0, 0, entry.length);
        entryNew[entry.length] = new MapEntry(key, value);
        entry = entryNew;
        //@ set map = \dl_mapUpdate(map, key, value);
        return null;
    }

    public Object put(Object key, Object value) {
        int index = getIndexOfKey(key);
        if (index == -1) {
            return putNotInDomain(key, value);

        } else {
            return putInDomain(index, value);
        }
    }

    void removeCopy(MapEntry[] entryNew, int index) {
        copyMapEntries(entryNew, 0, 0, index - 1);
        copyMapEntries(entryNew, index, index + 1, entry.length - index);
    }

    Object removeInDomain(int index) {
        Object ret = entry[index].value;
        MapEntry[] entryNew = getMapEntryArray(entry.length - 1);
        removeCopy(entryNew, index);
        entry = entryNew;
        //@ set map = \dl_mapRemove(map, entry[index].key);
        return ret;
    }

    public Object remove(Object key) {
        int index = getIndexOfKey(key);

        if (index == -1) {
            return null;
        } else {
            return removeInDomain(index);
        }
    }
    
    public int size() {
        return entry.length;
    }

}
