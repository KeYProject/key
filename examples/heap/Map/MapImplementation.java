package MapCaseStudy;

final class MapImplementation extends AbstractMap {

    /*@ normal_behaviour
     @ ensures map == \dl_mapEmpty();
     @*/
    public /*@pure@*/ MapImplementation() {
        clear();
    }
    
    public void clear() {
        entry = new MapEntry[0];
        //@ set map = \dl_mapEmpty();
        //@ set footprint = \all_fields(this);
    }

    public int size() {
        return entry.length;
    }

    public Object get(Object key) {
        int index = getIndexOfKey(key);
        if (index != -1) {
            return getValue(index);
        } else {
            return null;
        }
    }

    public boolean isEmpty() {
        return size() == 0;
    }

    public boolean containsKey(Object key) {
        return getIndexOfKey(key) != -1;
    }

    public boolean containsValue(Object value) {
        /*@ loop_invariant 0 <= i && i <= size();
         @ loop_invariant (\forall int x; 0 <= x && x < i; value != getValue(x));
         @ decreases size() - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < size(); i++) {
            if (value == getValue(i)) {
                return true;
            }
        }
        return false;
    }

    MapEntry[] getMapEntryArray(int l) {
        // This function is modeled after ArrayList.newArray()
        return new MapEntry[l];
    }

    int getIndexOfKey(Object key) {
        int index = -1;
        /*@ loop_invariant 0 <= i && i <= size();
         @ loop_invariant (index >= -1 && index < size());
         @ loop_invariant ((index > -1) ==> (getKey(index) == key
         @                                          && \dl_inDomain(map, key) 
         @                                          && i >= size() ));
         @ loop_invariant ((index == -1) ==> (\forall int x; x>=0 && x<i; getKey(x) != key));
         @ loop_invariant (\forall Object o; !\fresh(o));
         @ decreases size() - i;
         @ assignable \strictly_nothing;
         @*/
        for (int i = 0; i < size(); i++) {
            if (key == entry[i].key) {
                index = i;
                i = size();
            }
        }
        return index;
    }

    void copyMapEntries(Object[] target,
            int beginTarget,
            int beginEntry,
            int numberCopies) {
        /*@ loop_invariant 0 <= i && i <= numberCopies;
         @ loop_invariant ( \forall int x; 0 <= x && x < i; 
         @          ( target[beginTarget + x].equals(entry[beginEntry + x] )));
         @ loop_invariant (\forall Object o; !\fresh(o));
         @ decreases numberCopies - i;
         @ assignable target[beginTarget..beginTarget + numberCopies - 1];
         @*/
        for (int i = 0; i < numberCopies; i++) {
            target[beginTarget + i] = entry[beginEntry + i];
        }
    }

    Object putInDomain(int index, Object value) {
        Object ret = getValue(index);
        entry[index].value = value;
        //@ set map = \dl_mapUpdate(map, getKey(index), value);
        return ret;
    }

    Object putNotInDomain(Object key, Object value) {
        MapEntry[] entryNew = getMapEntryArray(size() + 1);
        copyMapEntries(entryNew, 0, 0, size());
        entryNew[size()] = new MapEntry(key, value);
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
        copyMapEntries(entryNew, index, index + 1, size() - index);
    }

    Object removeInDomain(int index) {
        Object ret = getValue(index);
        MapEntry[] entryNew = getMapEntryArray(size() - 1);
        removeCopy(entryNew, index);
        entry = entryNew;
        //@ set map = \dl_mapRemove(map, getKey(index));
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

    Object getKey(int index) {
        return entry[index].key;
    }

    Object getValue(int index) {
        return entry[index].value;
    }

}
