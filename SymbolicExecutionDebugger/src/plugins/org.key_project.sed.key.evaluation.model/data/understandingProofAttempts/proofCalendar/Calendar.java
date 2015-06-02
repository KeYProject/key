public class Calendar {
   private /*@ non_null @*/ Entry[] entries = new Entry[8];
   
   /*@ invariant entrySize >= 0 && entrySize < entries.length;
     @*/
   private int entrySize = 0;

   /*@ normal_behavior
     @ ensures entries[\old(entrySize)] == entry;
     @ ensures entrySize == \old(entrySize) + 1;
     @ assignable entries, entries[entrySize], entrySize;
     @*/
   public void addEntry(/*@ non_null @*/ Entry entry) {
      if (entrySize == entries.length) {
         Entry[] newEntries = new Entry[entries.length * 2];
         /*@ loop_invariant i >= 0 && i <= entries.length;
           @ loop_invariant (\forall int j; j >= 0 && j < i; 
           @                         newEntries[j] == entries[j]);
           @ decreasing entries.length - i;
           @ assignable newEntries[*], i;
           @*/
         for (int i = 0; i < entries.length; i++) {
            newEntries[i] = entries[i];
         }
         entries = newEntries;
      }
      entries[entrySize] = entry;
      entrySize++;
   }
   
   public static class Entry {
   }
}

