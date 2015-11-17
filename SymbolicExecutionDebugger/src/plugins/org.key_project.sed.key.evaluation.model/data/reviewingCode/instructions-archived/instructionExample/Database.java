public class Database {
   /*@ invariant entries != null;
     @ invariant \typeof(entries) == \type(Entry[]);
     @ invariant (\forall int i; 
     @                    i >= 0 && i < entries.length; 
     @                    entries[i] != null);
     @*/
   private Entry[] entries;

   public Database(Entry[] entries) {
      this.entries = entries;
   }

   /**
    * Accumulates the value of all {@link Entry} 
    * instances in the {@link Database} with help 
    * of the given {@link Accumulator}.
    * @param accumulator The {@link Accumulator} to use 
    *                which is not allowed to be {@code null}.
    * @return The computed accumulation.
    */
   public int accumulateDatabase(/*@ non_null @*/ 
                                 Accumulator accumulator) {
      int accumulation = 0;
      /*@ loop_invariant i >= 1 && i <= (entries.length + 1);
        @ decreasing entries.length - i;
        @ assignable accumulation, i;
        @*/
      for (int i = 1; i <= entries.length; i++) {
         accumulator.accumulate(accumulation, entries[i]);
      }
      return accumulation;
   }
}

class Entry {
   /*@ invariant value >= 0;
     @*/
   protected int value;

   protected /*@ nullable @*/ String description;

   protected /*@ non_null @*/ String id;
}

interface Accumulator {
   /*@ normal_behavior
     @ requires true;
     @ ensures true;
     @ assignable \everything;
     @*/
   public /*@ helper @*/ int accumulate(int accumulation, 
                                        Entry entry);
}