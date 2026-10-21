import java.util.Random;
public class LoanForUse {
    private static Random random = new Random();
    public final static int Inactive = 0;
    public final static int Proposal = 1;
    public final static int Consensus = 2;
    public final static int Finished = 3;
    public final static int End = 4;
    //@ public invariant -1 <= currentState < 5;
    public static int currentState = -1;
    //@ public static invariant code >= 0;
    public static int code;
    //@ public static invariant Lender_code >= 0;
    public static int Lender_code;
    //@ public static invariant Borrower_code >= 0;
    public static int Borrower_code;

    public static int Lender;
    public static int Borrower;

    public static int numLocker;
    //@ public static invariant timeLimit >= 0;
    public static int timeLimit;
    public static int value;
    //@ public static invariant now >= 0;
    public static int now = 0;
    //@ public static invariant DT_MIN.length == 2;
    //@ public static invariant DT_MAX.length == DT_MIN.length && DT_MIN != DT_MAX;
    //@ public static invariant (\forall int i; 0 <= i < DT_MIN.length; DT_MIN[i] <= DT_MAX[i]);
    public static int[] DT_MIN = new int[2];
    public static int[] DT_MAX = new int[2];

  // create unique name by prefixing function name tp parameter name
    public static int proposal_Locker_num;
    public static int proposal_Locker_c;


   //@ public static invariant ( timeLimit >= 0 && value >= 0 );
    /*@ model two_state static boolean assetPreservation() {
            return code + Lender_code + Borrower_code == \old(code + Lender_code + Borrower_code);
     } */
    // functions of the stipula contract
    /*@ public normal_behavior
      @ requires (true && Lender_code >= c);
      @ requires c >= 0 && Lender_code >= c;
      @ assignable code, Lender_code, numLocker;
      @ ensures code == \old(code + c) && Lender_code == \old(Lender_code - c) && numLocker == num;
      @ ensures assetPreservation();
      @*/
    public static void proposal_Locker(int num, int c) {
        numLocker = num;
        int tmp_0 = c; Lender_code = Lender_code - tmp_0;code = code + tmp_0; // asset transfer
    }
    /*@ public normal_behavior
      @ requires (true);
      @ assignable \nothing, DT_MIN[0], DT_MAX[0];
      @ ensures true;
      @ ensures  ( \old(DT_MIN[0] == -1 && DT_MAX[0] == -1) ?
      @            DT_MIN[0] == now + timeLimit && DT_MAX[0] == now + timeLimit
      @            : (
      @                ( DT_MAX[0] == (now + timeLimit > \old(DT_MAX[0]) ?
      @                                            now + timeLimit :  \old(DT_MAX[0])))
      @                && DT_MIN[0] == \old(DT_MIN[0])
      @              )
      @          );
      @ ensures assetPreservation();
      @*/
    public static void declare_Agreement() {
        
        
      int new_time;
      new_time = now + timeLimit;
      if (DT_MIN[0] == -1 && DT_MAX[0] == -1) {
          DT_MIN[0] = new_time;
          DT_MAX[0] = new_time;
      } else if (DT_MAX[0] < new_time) {
          DT_MAX[0] = new_time;
      }
    }
    /*@ public normal_behavior
      @ requires (true);
      @ requires code >= code;
      @ assignable code, Lender_code;
      @ ensures code == 0 && Lender_code == \old(Lender_code + code);
      @ ensures assetPreservation();
      @*/
    public static void returnB() {
        int tmp_1 = code; code = code - tmp_1;Lender_code = Lender_code + tmp_1; // asset transfer
    }
    /*@ public normal_behavior
      @ requires (true);
      @ assignable \nothing, DT_MIN[1], DT_MAX[1];
      @ ensures true;
      @ ensures  ( \old(DT_MIN[1] == -1 && DT_MAX[1] == -1) ?
      @            DT_MIN[1] == now + 15 && DT_MAX[1] == now + 15
      @            : (
      @                ( DT_MAX[1] == (now + 15 > \old(DT_MAX[1]) ?
      @                                            now + 15 :  \old(DT_MAX[1])))
      @                && DT_MIN[1] == \old(DT_MIN[1])
      @              )
      @          );
      @ ensures assetPreservation();
      @*/
    public static void immediate_Return() {
        
      int new_time;
      new_time = now + 15;
      if (DT_MIN[1] == -1 && DT_MAX[1] == -1) {
          DT_MIN[1] = new_time;
          DT_MAX[1] = new_time;
      } else if (DT_MAX[1] < new_time) {
          DT_MAX[1] = new_time;
      }
    }
    // event functions
    /*@ public normal_behavior
      @ requires code >= code;
      @ assignable code, Lender_code;
      @ ensures code == 0 && Lender_code == \old(Lender_code + code);
      @ ensures code == 0 && Lender_code == \old(Lender_code + code);
      @ ensures assetPreservation();
      @*/
    public static void event_0() {
        
        
        int tmp_2 = code; code = code - tmp_2;Lender_code = Lender_code + tmp_2; // asset transfer
    }
    /*@ public normal_behavior
      @ requires code >= code;
      @ assignable code, Lender_code;
      @ ensures code == 0 && Lender_code == \old(Lender_code + code);
      @ ensures code == 0 && Lender_code == \old(Lender_code + code);
      @ ensures assetPreservation();
      @*/
    public static void event_1() {
        
        
        int tmp_3 = code; code = code - tmp_3;Lender_code = Lender_code + tmp_3; // asset transfer
    }
    // behavior
    /*@ public normal_behavior
      @ requires ( proposal_Locker_c >= 0 && code == 0 && Borrower_code == 0 );
      @ ensures  ( assetPreservation() ) && ( currentState == Finished ==> (Lender_code == \old(Lender_code) && code == 0) );
      @ assignable \everything;
      @*/
    public static void behavior() {
        currentState = -1;
        resetDispatch();
        GenInactive();
    }

    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenInactive() {
        currentState = Inactive;
        int next_action = computeNextStepEmptyEvents(1);
        //@ assume next_action < 0 || (next_action > 0 ? Inactive_evalConditionFor(next_action) : false);
        switch (next_action) {
          case 1:
            proposal_Locker(proposal_Locker_num, proposal_Locker_c);
            GenProposal();
            break;
          default: break;
        }
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenProposal() {
        currentState = Proposal;
        int next_action = computeNextStepEmptyEvents(1);
        switch (next_action) {
          case 1:
            declare_Agreement();
            GenConsensus();
            break;
          default: break;
        }
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenConsensus() {
        currentState = Consensus;
        int next_action = computeNextStep(2, new int[] { 0, 1 });
        switch (next_action) {
          case 1:
            returnB();
            GenFinished();
            break;
          case 2:
            immediate_Return();
            GenEnd();
            break;
          case -1:
            event_0();
            DT_MIN[0] = -1;
            DT_MAX[0] = -1;
            GenFinished();
            break;
          case -2:
            event_1();
            DT_MIN[1] = -1;
            DT_MAX[1] = -1;
            GenFinished();
            break;
          default: break;
        }
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenFinished() {
        currentState = Finished;
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenEnd() {
        currentState = End;
    }



    // auxiliary methods
    public final static int computeNextStepNoFunctions(int[] events){
        int entry = minTimeEntry(events);
        if (entry == -1) {
            return -(events.length + 1);
        } else if (DT_MIN[entry] >= now) {
                now = DT_MIN[entry];
        }
        return -(entry + 1);
    }
    public final static int computeNextStepEmptyEvents(int nrFct){
        if (nrFct == 0) {
            return -1;
        } else {
            int max_entry = maxTimeEntry();
            int max_time = max_entry == -1 ? now : DT_MAX[max_entry] + 1;
            int u_Q = choose(now, max_time);
            now = u_Q;
            return choose(1,nrFct);
        }
    }
    public final static int computeNextStep(int nrFct, int[] events){
        int w_Q;
        int entry = minTimeEntry(events);
        int max_entry = maxTimeEntry();
        int max_time = (max_entry == -1 ? now : DT_MAX[max_entry] + 1);
        int u_Q = choose(now, max_time);
        if (entry == -1) {
            w_Q = choose(1,nrFct);
            now = u_Q;
            return w_Q;
        } else {
           int dtMaxEntry = DT_MAX[entry];
           int dtMinEntry = DT_MIN[entry];
           if ((dtMinEntry == now) ? true : (dtMaxEntry == now)) {
             return -(entry + 1);
           } else {
               w_Q = choose(0, nrFct);
               if (w_Q != 0) {
                   int timeval = maxSafeTimeIncrement(events);
                   now = (dtMinEntry < now ? min(dtMinEntry - 1, u_Q) : min(max(timeval-1, now), u_Q));
                   return w_Q;
               } else {
                   now = (dtMinEntry < now ? now : dtMinEntry);
                   return -(entry + 1);
               }
           }
        }
    }
    /*@ public normal_behavior
      @ requires DT_MIN != null && DT_MAX != null & DT_MIN.length == DT_MAX.length;
      @ requires events.length <= DT_MIN.length;
      @ requires (\forall int i; 0 <= i < events.length; 0 <= events[i] < DT_MIN.length);
      @ requires  (\forall int i; 0 <= i < DT_MIN.length; DT_MIN[i] <= DT_MAX[i]);
      @ requires now >= 0;
      @ ensures \result == -1 || \result >= now;
      @ ensures \result == -1 <==> (\forall int i; 0 <= i < events.length; DT_MAX[events[i]] < now );
      @ ensures \result >= now ==>
      @              (\exists int i; 0 <= i < events.length; \result == DT_MIN[events[i]] || \result == DT_MAX[events[i]])
      @           && (\forall int i; 0 <= i < events.length;
      @                               (DT_MIN[events[i]] >= now ==> \result <= DT_MIN[events[i]])
      @                            && (DT_MIN[events[i]] < now && DT_MAX[events[i]] >= now ==> \result <= DT_MAX[events[i]]));
      @ assignable \strictly_nothing;
      @
      @*/
    public /*@ helper @*/ static int maxSafeTimeIncrement(int[] events) {
        int res = -1;
        /*@ loop_invariant 0 <= j <= events.length;
          @ loop_invariant res == -1 || res >= now;
          @ loop_invariant res == -1 <==> (\forall int i; 0 <= i < j; DT_MAX[events[i]] < now );
          @ loop_invariant res >= now ==>
          @              (\exists int i; 0 <= i < j; (res == DT_MIN[events[i]]) || (res == DT_MAX[events[i]]))
          @           && (\forall int i; 0 <= i < j;
          @                               (DT_MIN[events[i]] >= now ==> res <= DT_MIN[events[i]])
          @                            && (DT_MIN[events[i]] < now && DT_MAX[events[i]] >= now ==> res <= DT_MAX[events[i]]));
          @ assignable \strictly_nothing;
          @ decreases events.length - j;
          @*/
        for (int j = 0; j < events.length; j++) {
            final int event = events[j];
            if (res == -1 && DT_MAX[event] >= now) {
               res = DT_MAX[event];
            }
            if (DT_MIN[event] >= now && res > DT_MIN[event]) {
                res = DT_MIN[event];
            } else if (DT_MIN[event] < now && DT_MAX[event] >= now && res > DT_MAX[event]) {
                    res = DT_MAX[event];
            }
        }
        return res;
    }
    // while proving we only use the contract and hence have a non-deterministic choice
    // executing the implementation chooses a value randomly
    /*@ public normal_behavior
      @ requires random != null;
      @ requires -1 <= lower <= upper;
      @ ensures lower <= \result <= upper;
      @ assignable \nothing;
     */
    private /*@ helper @*/ static int choose(int lower, int upper) {
        return random.nextInt(upper + 1 - lower) + lower;
    }
    /**
     * Note: note implementation is deterministic, non-deterministic behavior by underspecification
     *  in contract only
     */
    /*@ public normal_behavior
      @ requires DT_MIN != null && DT_MAX != null & DT_MIN.length == DT_MAX.length;
      @ requires events.length <= DT_MIN.length;
      @ requires (\forall int i; 0 <= i < events.length; 0 <= events[i] < DT_MIN.length);
      @ requires (\forall int i; 0 <= i < DT_MIN.length; DT_MIN[i] <= DT_MAX[i]);
      @ ensures -1 <= \result < DT_MIN.length;
      @ ensures \result == -1 <==> (\forall int i; 0 <= i < events.length; DT_MAX[events[i]] < now);
      @ ensures \result != -1 ==>
      @         ( DT_MAX[\result] >= now
      @           && (\forall int j; 0 <= j < events.length;
      @                      ((DT_MIN[events[j]] < now && DT_MAX[events[j]] >= now) ==> DT_MIN[\result] <= DT_MAX[events[j]])
      @                   && (DT_MIN[events[j]] >= now ==> DT_MIN[\result] <= DT_MIN[events[j]])
      @               )
      @           && (\exists int j; 0 <= j < events.length; \result == events[j])
      @         );
      @ assignable \strictly_nothing;
      @*/
    public static /*@ helper @*/ int minTimeEntry(int[] events) {
        if (events.length == 0) {
            return -1;
        }
        int minEvent = -1;
        /*@ loop_invariant
          @       0 <= i <= events.length
          @   && -1 <= minEvent < DT_MIN.length
          @   && (minEvent == -1 ? (\forall int j; 0 <= j < i; DT_MAX[events[j]] < now) :
          @         ( DT_MAX[minEvent] >= now
          @           && (\forall int j; 0 <= j < i;
          @                  ((DT_MIN[events[j]] < now && DT_MAX[events[j]] >= now) ==> DT_MIN[minEvent] <= DT_MAX[events[j]])
          @               && (DT_MIN[events[j]] >= now ==> DT_MIN[minEvent] <= DT_MIN[events[j]])
          @               )
          @           && (\exists int j; 0 <= j < i; minEvent == events[j]) )
          @       );
          @ assignable \strictly_nothing;
          @ decreases events.length - i;
         */
        for (int i = 0; i < events.length; i++) {
            if (DT_MAX[events[i]] >= now) {
              if (minEvent == -1) {
                  minEvent = events[i];
              } else if (DT_MIN[events[i]] < now && DT_MAX[events[i]] >= now && DT_MAX[events[i]] < DT_MIN[minEvent]) {
                  minEvent = events[i];
              } else if (DT_MIN[events[i]]  >= now && DT_MIN[minEvent] > DT_MIN[events[i]]) {
                  minEvent = events[i];
              }
            }
        }
        return minEvent;
    }
    /**
     * Note: note implementation is deterministic, non-deterministic behavior by underspecification
     *  in contract only
     */
    /*@ public normal_behavior
      @ requires DT_MAX != null;
      @ ensures -1 <= \result < DT_MAX.length;
      @ ensures \result != -1 ==> (DT_MAX.length > 0 && DT_MAX[\result] >= now &&
      @                            (\forall int j; 0 <= j < DT_MAX.length; DT_MAX[j] <= DT_MAX[\result]));
      @ ensures \result == -1 <==> (\forall int j; 0 <= j < DT_MAX.length; DT_MAX[j] < now);
      @ assignable \strictly_nothing;
     */
    public static /*@ helper @*/ int maxTimeEntry() {
        if (DT_MAX.length == 0) {
            return -1;
        }
        int maxEntry = -1;
        /*@ loop_invariant
          @   i >= 0 && i <= DT_MAX.length &&
          @   -1 <= maxEntry < DT_MAX.length &&
          @   (maxEntry != -1 ==> (DT_MAX[maxEntry] >= now && ( \forall int j; 0 <= j < i; DT_MAX[maxEntry] >= DT_MAX[j]))) &&
          @   (maxEntry == -1 <==> ( \forall int j; 0 <= j < i; DT_MAX[j] < now));
          @ assignable \strictly_nothing;
          @ decreases DT_MAX.length - i;
         */
        for (int i = 0; i < DT_MAX.length; i++) {
            if (DT_MAX[i] >= now && (maxEntry == -1 || DT_MAX[i] > DT_MAX[maxEntry])) {
               maxEntry = i;
            }
        }
        return maxEntry;
    }
    /*@ private normal_behavior
      @ requires DT_MIN != null && DT_MAX != null && DT_MIN.length == DT_MAX.length;
      @ ensures (\forall int i; 0 <= i < DT_MIN.length; DT_MIN[i] == -1);
      @ ensures (\forall int i; 0 <= i < DT_MAX.length; DT_MAX[i] == -1);
      @ assignable DT_MIN[*], DT_MAX[*];
      @*/
    private static /*@ helper @*/ void resetDispatch() {
        /*@ loop_invariant
          @   0 <= i <= DT_MIN.length
          @   && (\forall int j; 0 <= j < i; DT_MIN[j] == -1)
          @   && (\forall int j; 0 <= j < i; DT_MAX[j] == -1);
          @ assignable DT_MIN[*], DT_MAX[*];
          @ decreases DT_MIN.length - i;
          @*/
        for (int i = 0; i < DT_MIN.length; i++) {
            DT_MIN[i] = -1;
            DT_MAX[i] = -1;
        }
    }
    /*@ public normal_behavior
      @ ensures \result == (a <= b ? a : b);
      @ assignable \strictly_nothing;
     */
    public static /*@ helper @*/ int min(int a, int b) {
        return (a <= b) ? a : b;
    }
    /*@ public normal_behavior
      @ ensures \result == (a >= b ? a : b);
      @ assignable \strictly_nothing;
     */
    public static /*@ helper @*/ int max(int a, int b) {
        return (a >= b) ? a : b;
    }
    /*@ public normal_behavior
      @ requires (\forall int j; 0 <= j < e.length; e[j] >= 0);
      @ ensures e.length > 0 ? ((\forall int j; 0 <= j < e.length; \result >= e[j])
      @          && (\exists int j; 0 <= j < e.length; \result == e[j])) : \result == 0;
      @ assignable \strictly_nothing;
     */
    public static /*@ helper @*/ int max(int[] e) {
        int max = 0;
        /*@ loop_invariant
          @   i >= 0 && i <= e.length
          @   && (\forall int j; 0 <= j < i; max >= e[j])
          @   && (i>0 ==> (\exists int j; 0 <= j < i; max == e[j]))
          @   && (i == 0 ==> max == 0) ;
          @ assignable \strictly_nothing;
          @ decreases e.length - i;
         */
        for (int i = 0; i < e.length; i++) {
            if (max < e[i]) {
                max = e[i];
            }
        }
        return max;
    }
// evaluating function conditions
 
    private static boolean proposal_Locker_cond(int num, int c) {
        return (true && Lender_code >= c);
    }



    private static boolean Inactive_evalConditionFor(int fct) {
        switch(fct) {
          case 1: return proposal_Locker_cond(proposal_Locker_num, proposal_Locker_c);
          default: return false;
        }
    }

    private static boolean Proposal_evalConditionFor(int fct) {
        return true;
    }

    private static boolean Consensus_evalConditionFor(int fct) {
        return true;
    }


}