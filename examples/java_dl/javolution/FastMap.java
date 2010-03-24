import javax.realtime.*;

public class FastMap{

    /**
     * Holds table higher index rotation. 
     */
    static final int R0 = 5;

    /*@ public invariant \memoryArea(_head)==\memoryArea(_tail) && 
      @    \memoryArea(this)==\memoryArea(_tail);
      @*/

    /**
     * Holds the table lower index mask. 
     */
    static final int M0 = (1 << R0) - 1;

    /**
     * Holds the map's hash table.
     * Use two dimensional arrays to avoid large arrays allocations. 
     */
    transient Entry[][] _entries;

    /**
     * Holds the head entry to which the first entry attaches.
     * The head entry never changes (entries always added last).
     */
    transient Entry _head;

    /**
     * Holds the tail entry to which the last entry attaches.
     * The tail entry changes as entries are added/removed.
     */
    transient Entry _tail;

    public FastMap(int capacity) {
        setup(capacity);
    }

   /*@ public normal_behavior
     @  requires capacity <= (1 << R0) && capacity>=0 && 
     @     \memoryArea(this)==\currentMemoryArea;
     @  working_space \space(Entry[1][1<<R0]) + 
     @     (2+capacity)*\space(Entry);
     @ also public normal_behavior
     @  requires capacity > (1 << R0) && capacity<1<<24 && 
     @     \memoryArea(this)==\currentMemoryArea && \currentMemoryArea.consumed==0;
     @  working_space \space(Entry[(2*capacity)>> R0][1<<R0])+
     @     (2+capacity)*\space(Entry);
     @*/
    private void setup(int capacity) {
        int tableLength = 1 << R0;
	/*@ loop_invariant 1 << R0 < capacity ? 
	  @     tableLength>=1 << R0 && tableLength<2*capacity : 
	  @     tableLength == 1 << R0;
	  @ decreases 1 << R0 < capacity ? 2*capacity-2-tableLength : 0;
	  @ assignable tableLength;
	  @ working_space_single_iteration 0;
	  @*/
        while (tableLength < capacity) {
            tableLength <<= 1;
        }
	int size = tableLength >> R0;
        _entries = (Entry/*<K,V>*/[][]) new Entry[size][];
	int i = 0;
	/*@ loop_invariant i>=0 && i<=_entries.length;
	  @ decreases _entries.length-i;
	  @ assignable i, _entries[*];
	  @ working_space_single_iteration \space(Entry[1 << R0]);
	  @*/
        while (i < _entries.length) {
	    int blockLength = 1 << R0;
            _entries[i++] = (Entry/*<K,V>*/[]) new Entry[blockLength];
        }
        _head = new Entry();
        _tail = new Entry();
        _head._next = _tail;
        _tail._previous = _head;
        Entry previous = _tail;
	i = 0;
	/*@ loop_invariant i>=0 && previous!=null && i<=capacity;
	  @ decreases capacity-i;
	  @ assignable _tail._next, i;
	  @ working_space_single_iteration \space(Entry);
	  @*/
        while(i++ < capacity) {
            Entry newEntry = new Entry();
            newEntry._previous = previous;
            previous._next = newEntry;
            previous = newEntry;
        }
    }

    public final Object/*{V}*/put(MyObject/*{K}*/key, MyObject/*{V}*/value) {
        addEntry(key.hashCode(), key, value);
    }

    private void addEntry(int hash, Object/*{K}*/key, Object/*{V}*/value) {
        if (_tail._next == null) {
            increaseCapacity();
        }
        final Entry newTail = _tail._next;
        // Setups entry parameters.
        _tail._key = key;
        _tail._value = value;
        _tail._keyHash = hash;
        _tail._table = _entries;
	// Connects to bucket ...
    }

    private void increaseCapacity() {
        MemoryArea.getMemoryArea(this).executeInArea(new Runnable() {
            public void run() {
                Entry newEntry0 = new Entry();
                _tail._next = newEntry0;
                newEntry0._previous = _tail;

                Entry newEntry1 = new Entry();
                newEntry0._next = newEntry1;
                newEntry1._previous = newEntry0;

                Entry newEntry2 = new Entry();
                newEntry1._next = newEntry2;
                newEntry2._previous = newEntry1;

                Entry newEntry3 = new Entry();
                newEntry2._next = newEntry3;
                newEntry3._previous = newEntry2;
            }
        });
    }

}
