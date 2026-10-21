import java.util.Random;
public class DonationMatching {
    private static Random random = new Random();
    public final static int Start = 0;
    public final static int Collect = 1;
    public final static int End = 2;
    //@ public invariant -1 <= currentState < 3;
    public static int currentState = -1;
    //@ public static invariant wallet >= 0;
    public static int wallet;
    //@ public static invariant Company_wallet >= 0;
    public static int Company_wallet;
    //@ public static invariant Employee_wallet >= 0;
    public static int Employee_wallet;

    public static int Company;
    public static int Employee;

    //@ public static invariant endTime >= 0;
    public static int endTime;
    public static int amount;
    public static int matchAmount;
    public static int donationSize;
    //@ public static invariant now >= 0;
    public static int now = 0;
    //@ public static invariant DT_MIN.length == 1;
    //@ public static invariant DT_MAX.length == DT_MIN.length && DT_MIN != DT_MAX;
    //@ public static invariant (\forall int i; 0 <= i < DT_MIN.length; DT_MIN[i] <= DT_MAX[i]);
    public static int[] DT_MIN = new int[1];
    public static int[] DT_MAX = new int[1];
    public static final int MAX_ITE_Collect  = 20;

    public static int start_w;
    public static int donate_w;
   //@ public static invariant ( endTime == 10 && amount == 100 && matchAmount == 200 && donationSize == 10 );
    /*@ model two_state static boolean assetPreservation() {
            return wallet + Company_wallet + Employee_wallet == \old(wallet + Company_wallet + Employee_wallet);
     } */
    // functions of the stipula contract
    /*@ public normal_behavior
      @ requires ((w == matchAmount) && Company_wallet >= w);
      @ requires w >= 0 && Company_wallet >= w;
      @ assignable wallet, Company_wallet, DT_MIN[0], DT_MAX[0];
      @ ensures wallet == \old(wallet + w) && Company_wallet == \old(Company_wallet - w);
      @ ensures  ( \old(DT_MIN[0] == -1 && DT_MAX[0] == -1) ?
      @            DT_MIN[0] == now + endTime && DT_MAX[0] == now + endTime
      @            : (
      @                ( DT_MAX[0] == (now + endTime > \old(DT_MAX[0]) ?
      @                                            now + endTime :  \old(DT_MAX[0])))
      @                && DT_MIN[0] == \old(DT_MIN[0])
      @              )
      @          );
      @ ensures assetPreservation();
      @*/
    public static void start(int w) {
        int tmp_0 = w; Company_wallet = Company_wallet - tmp_0;wallet = wallet + tmp_0; // asset transfer
      int new_time;
      new_time = now + endTime;
      if (DT_MIN[0] == -1 && DT_MAX[0] == -1) {
          DT_MIN[0] = new_time;
          DT_MAX[0] = new_time;
      } else if (DT_MAX[0] < new_time) {
          DT_MAX[0] = new_time;
      }
    }
    /*@ public normal_behavior
      @ requires (true && Employee_wallet >= w);
      @ requires w >= 0 && Employee_wallet >= w;
      @ assignable Employee_wallet, wallet;
      @ ensures Employee_wallet == \old(Employee_wallet - w) && wallet == \old(wallet + w);
      @ ensures assetPreservation();
      @*/
    public static void donate(int w) {
        int tmp_1 = w; Employee_wallet = Employee_wallet - tmp_1;wallet = wallet + tmp_1; // asset transfer
    }
    // event functions
    /*@ public normal_behavior
      @ assignable Company_wallet, wallet;
      @ ensures Company_wallet == \old(((wallet >= matchAmount) && (wallet < (matchAmount + amount))) ? (Company_wallet + matchAmount) : Company_wallet) && wallet == \old(((wallet >= matchAmount) && (wallet < (matchAmount + amount))) ? (wallet - matchAmount) : wallet);
      @ ensures Company_wallet == \old(((wallet >= matchAmount) && (wallet < (matchAmount + amount))) ? (Company_wallet + matchAmount) : Company_wallet) && wallet == \old(((wallet >= matchAmount) && (wallet < (matchAmount + amount))) ? (wallet - matchAmount) : wallet);
      @ ensures assetPreservation();
      @*/
    public static void event_0() {
        if (((wallet >= matchAmount) && (wallet < (matchAmount + amount)))) {
		 int tmp_2 = matchAmount; wallet = wallet - tmp_2;Company_wallet = Company_wallet + tmp_2; // asset transfer
		} 
    }
    // behavior
    /*@ public normal_behavior
      @ requires ( Employee_wallet > 20 * donationSize ) && ( Company_wallet > matchAmount && wallet == 0 ) && ( start_w == matchAmount && donate_w == donationSize );
      @ ensures  ( wallet < amount ==> Company_wallet == \old(Company_wallet) ) && ( wallet >= amount ==> Company_wallet == \old(Company_wallet) - matchAmount );
      @ assignable \everything;
      @*/
    public static void behavior() {
        currentState = -1;
        resetDispatch();
        GenStart();
    }

    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenStart() {
        currentState = Start;
        int next_action = computeNextStepEmptyEvents(1);
        //@ assume next_action < 0 || (next_action > 0 ? Start_evalConditionFor(next_action) : false);
        switch (next_action) {
          case 1:
            start(start_w);
            GenCollect();
            break;
          default: break;
        }
    }

    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenEnd() {
        currentState = End;
    }

    // GEN_C(Q) for initial state of a cycle
    public static void GenCollect() {
        currentState = Collect;
        int op = executeCycleCollect();
        switch(-(op + 1)) {
          case 0:
            event_0();
            DT_MIN[0] = -1;
            DT_MAX[0] = -1;
            GenEnd();
            break;
          default: break;
        }
    }

    public static int executeCycleCollect() {
        int count = 0;
        int op    = 1;
        int[] stateEvents = new int[] { 0 };
        /*@ loop_invariant 0 <= count <= MAX_ITE_Collect;
          @ loop_invariant currentState == Collect;
          @ loop_invariant ( 0 <= Employee_wallet <= \old(Employee_wallet) );
          @ loop_invariant ( \old(Employee_wallet) + \old(wallet) == Employee_wallet + wallet );
          @ loop_invariant ( Employee_wallet >= (MAX_ITE_Collect - count) * donationSize );
          @ loop_invariant ( \old(now) <= now <= \old(now) + endTime );
          @ loop_invariant ( 0 < op <= 1 || -2 <= op <= -1 );
          @ assignable wallet, Employee_wallet, now;
          @ decreases MAX_ITE_Collect - count;
          @*/
        while (count < MAX_ITE_Collect &&  op > 0) {
            switch (op) {
                case 1:
                  donate(donate_w);
                  break;
                default: throw new RuntimeException("Should never be reached.");
           }
           currentState = Collect;
           op = computeNextStep(1, stateEvents);
           //@ assume op < 0 || (op > 0 ? Collect_evalConditionFor(op) : false);
           count += 1;
        }
        if (op < 0) {
            return op;
        } else {
            return computeNextStepNoFunctions(stateEvents);
        }
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
 
    private static boolean start_cond(int w) {
        return ((w == matchAmount) && Company_wallet >= w);
    }
 
    private static boolean donate_cond(int w) {
        return (true && Employee_wallet >= w);
    }

    private static boolean Start_evalConditionFor(int fct) {
        switch(fct) {
          case 1: return start_cond(start_w);
          default: return false;
        }
    }

    private static boolean Collect_evalConditionFor(int fct) {
        switch(fct) {
          case 1: return donate_cond(donate_w);
          default: return false;
        }
    }

}