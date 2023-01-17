public class Calendar {
   protected /*@ non_null @*/ Entry[] entries = new Entry[8];
   
   /*@ invariant entrySize >= 0 && entrySize < entries.length;
     @*/
   protected int entrySize = 0;

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
            //XXX: Loop Body Termination (of the 'Body Preserves Invariant' branch)
         }
         entries = newEntries;
         //XXX: Continuation After Then
      }
      else {
         //XXX: Continuation After Else
      }
      entries[entrySize] = entry;
      entrySize++;
   }
   
   public static class Entry {
   }
}

