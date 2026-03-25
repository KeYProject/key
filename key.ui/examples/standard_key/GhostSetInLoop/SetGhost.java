import java.util.List;

public class SetGhost {
    /*@ public normal_behavior
      @ requires \invariant_for(l);
      @ ensures \result == l.seq.length;
      @*/
    static int counter(List l) {
        int listSize = l.size();
        int counter = 0;
        //@ ghost int iter;
        //@ set iter = 0;

        /*@ loop_invariant
          @ i >= 0 && i <= listSize && listSize == l.size()
          @  && i == counter
          @  && iter == counter
          @ ;
          @ decreases listSize - i;
          @ assignable counter,iter;
          @*/
        for (int i = 0; i < listSize; i++) {
            counter++;
            //@ set iter = iter + 1;
            //@ assert iter == 1;
            assert counter == 1;
        }
        //@ assert iter == counter;
        return counter;
    }
}