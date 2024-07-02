
public class ImmutableList {
   private final /*@ nullable @*/ ImmutableList next;

   public ImmutableList(/*@ nullable @*/ ImmutableList next) {
      this.next = next;
   }
   
   /*@ normal_behavior
     @ requires next != null;
     @ requires next.next != null;
     @ ensures \result != this;
     @ assignable \nothing;
     @*/
   public ImmutableList down2() {
      ImmutableList current = next;
      /*@ loop_invariant i >= 1 && i <= 2;
        @ loop_invariant current != null;
        @ loop_invariant current != this;
        @ decreasing i;
        @ assignable i, current;
        @*/
      for (int i = 1; i < 2; i++) {
         current = current.next;
      }
      return current;
   }
}
