// import java.util.Random;
public class Deposit {
    // private static Random random = new Random();
    public final static int Start = 0;
    public final static int Run = 1;
    public final static int End = 2;
    //@ public invariant -1 <= currentState < 3;
    public static int currentState = -1;
    //@ public static invariant flour >= 0;
    public static int flour;
    //@ public static invariant Client_flour >= 0;
    public static int Client_flour;
    //@ public static invariant Farm_flour >= 0;
    public static int Farm_flour;
    //@ public static invariant wallet >= 0;
    public static int wallet;
    //@ public static invariant Client_wallet >= 0;
    public static int Client_wallet;
    //@ public static invariant Farm_wallet >= 0;
    public static int Farm_wallet;

    public static int Client;
    public static int Farm;

    public static int cost_flour;
    //@ public static invariant now >= 0;
    public static int now = 0;
    //@ public static invariant DT_MIN.length == 1;
    //@ public static invariant DT_MAX.length == DT_MIN.length && DT_MIN != DT_MAX;
    //@ public static invariant (\forall int i; 0 <= i < DT_MIN.length; DT_MIN[i] <= DT_MAX[i]);
    public static int[] DT_MIN = new int[1];
    public static int[] DT_MAX = new int[1];
    public static int MAX_ITE_Run;
    //@ public static invariant MAX_ITE_Run > 0;

    public static int begin_h;
    public static int send_sh;
    public static int buy_w;
   //@ public static invariant ( cost_flour > 0 );
    /*@ model two_state static boolean assetPreservation() {
            return flour + Client_flour + Farm_flour == \old(flour + Client_flour + Farm_flour) && flour + Client_flour + Farm_flour + wallet + Client_wallet + Farm_wallet == \old(flour + Client_flour + Farm_flour + wallet + Client_wallet + Farm_wallet);
     } */
    // functions of the stipula contract
    /*@ public normal_behavior
      @ requires (true && Farm_flour >= h);
      @ requires h >= 0 && Farm_flour >= h;
      @ assignable Farm_flour, flour, DT_MIN[0], DT_MAX[0];
      @ ensures Farm_flour == \old(Farm_flour - h) && flour == \old(flour + h);
      @ ensures  ( \old(DT_MIN[0] == -1 && DT_MAX[0] == -1) ?
      @            DT_MIN[0] == now + 365 && DT_MAX[0] == now + 365
      @            : (
      @                ( DT_MAX[0] == (now + 365 > \old(DT_MAX[0]) ?
      @                                            now + 365 :  \old(DT_MAX[0])))
      @                && DT_MIN[0] == \old(DT_MIN[0])
      @              )
      @          );
      @ ensures assetPreservation();
      @*/
    public static void begin(int h) {
        
        int tmp_0 = h; Farm_flour = Farm_flour - tmp_0;flour = flour + tmp_0; // asset transfer
      int new_time;
      new_time = now + 365;
      if (DT_MIN[0] == -1 && DT_MAX[0] == -1) {
          DT_MIN[0] = new_time;
          DT_MAX[0] = new_time;
      } else if (DT_MAX[0] < new_time) {
          DT_MAX[0] = new_time;
      }
    }
    /*@ public normal_behavior
      @ requires (true && Farm_flour >= sh);
      @ requires sh >= 0 && Farm_flour >= sh;
      @ assignable Farm_flour, flour;
      @ ensures Farm_flour == \old(Farm_flour - sh) && flour == \old(flour + sh);
      @ ensures assetPreservation();
      @*/
    public static void send(int sh) {
        
        int tmp_1 = sh; Farm_flour = Farm_flour - tmp_1;flour = flour + tmp_1; // asset transfer
    }
    /*@ public normal_behavior
      @ requires ((w <= (flour * cost_flour)) && Client_wallet >= w);
      @ requires w >= 0 && Client_wallet >= w && flour >= (w / cost_flour) && wallet >= wallet;
      @ assignable Client_flour, wallet, Farm_wallet, Client_wallet, flour;
      @ ensures Client_flour == \old(Client_flour + (w / cost_flour)) && wallet == 0 && Farm_wallet == \old(Farm_wallet + (wallet + w)) && Client_wallet == \old(Client_wallet - w) && flour == \old(flour - (w / cost_flour));
      @ ensures assetPreservation();
      @*/
    public static void buy(int w) {
        int tmp_2 = w; Client_wallet = Client_wallet - tmp_2;wallet = wallet + tmp_2; // asset transfer
        int tmp_3 = (w / cost_flour); flour = flour - tmp_3;Client_flour = Client_flour + tmp_3; // asset transfer
        int tmp_4 = wallet; wallet = wallet - tmp_4;Farm_wallet = Farm_wallet + tmp_4; // asset transfer
    }
    // event functions
    /*@ public normal_behavior
      @ requires flour >= flour;
      @ assignable Farm_flour, flour;
      @ ensures Farm_flour == \old(Farm_flour + flour) && flour == 0;
      @ ensures Farm_flour == \old(Farm_flour + flour) && flour == 0;
      @ ensures assetPreservation();
      @*/
    public static void event_0() {
        int tmp_5 = flour; flour = flour - tmp_5;Farm_flour = Farm_flour + tmp_5; // asset transfer
    }
    // behavior
    /*@ public normal_behavior
      @ requires ( Farm_wallet >= 0 && Client_wallet > 0 ) && ( Farm_flour > 0 && Client_flour == 0 ) && ( Farm_flour > MAX_ITE_Run * send_sh + begin_h ) && ( Client_wallet > MAX_ITE_Run * cost_flour * Farm_flour ) && ( wallet == 0 && flour == 0 ) && ( begin_h >= 0 && begin_h <= Farm_flour ) && ( send_sh >= 0 && send_sh <= Farm_flour ) && ( 0 <= buy_w * (MAX_ITE_Run+1) < Client_wallet ) && ( buy_w * cost_flour <= begin_h );
      @ ensures  ( \old(Client_wallet) - Client_wallet >= cost_flour*(Client_flour - \old(Client_flour)) ) && ( Farm_wallet - \old(Farm_wallet) >= cost_flour*(\old(Farm_flour) - Farm_flour) );
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
            begin(begin_h);
            GenRun();
            break;
          default: break;
        }
    }

    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenEnd() {
        currentState = End;
    }

    // GEN_C(Q) for initial state of a cycle
    public static void GenRun() {
        currentState = Run;
        int op = executeCycleRun();
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

    public static int executeCycleRun() {
        int count = 0;
        int op    = 1;
        int[] stateEvents = new int[] { 0 };
        /*@ loop_invariant 0 <= count <= MAX_ITE_Run;
          @ loop_invariant currentState == Run;
          @ loop_invariant ( 0 <= flour && 0 <= Client_flour );
          @ loop_invariant ( 0 <= Farm_flour <= \old(Farm_flour) );
          @ loop_invariant ( 0 == wallet && 0 <= Farm_wallet );
          @ loop_invariant ( 0 <= Client_wallet <= \old(Client_wallet) );
          @ loop_invariant ( 0 <= Farm_flour <= \old(Farm_flour) );
          @ loop_invariant ( Client_flour  <= count * (buy_w / cost_flour) );
          @ loop_invariant ( Farm_flour    > (MAX_ITE_Run - count) * send_sh );
          @ loop_invariant ( Client_wallet > (MAX_ITE_Run - count) * buy_w );
          @ loop_invariant ( \old(Client_wallet) - Client_wallet >= cost_flour*(Client_flour - \old(Client_flour)) );
          @ loop_invariant ( Farm_wallet - \old(Farm_wallet) >= cost_flour*(\old(Farm_flour) - Farm_flour - (flour - \old(flour))) );
          @ loop_invariant ( assetPreservation() );
          @ loop_invariant ( \old(now) <= now <= \old(now) + 365 );
          @ loop_invariant ( -1 <= op <= 2 && op != 0 && (op > 0 ==> Run_evalConditionFor(op)) );
          @ assignable flour, Farm_flour, Client_flour, Farm_wallet, Client_wallet, now;
          @ decreases MAX_ITE_Run - count;
          @*/
        while (count < MAX_ITE_Run &&  op > 0) {
            switch (op) {
                case 1:
                  send(send_sh);
                  break;
                case 2:
                  buy(buy_w);
                  break;
                default: throw new RuntimeException("Should never be reached.");
           }
           currentState = Run;
           op = computeNextStep(2, stateEvents);
           //@ assume op < 0 || (op > 0 ? Run_evalConditionFor(op) : false);
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
      @ requires -1 <= lower <= upper;
      @ ensures lower <= \result <= upper;
      @ assignable \nothing;
     */
    private /*@ helper @*/ static int choose(int lower, int upper) {
        return lower; //random.nextInt(upper + 1 - lower) + lower;
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
 
    private static boolean begin_cond(int h) {
        return (true && Farm_flour >= h);
    }
 
    private static boolean send_cond(int sh) {
        return (true && Farm_flour >= sh);
    }
 
    private static boolean buy_cond(int w) {
        return ((w <= (flour * cost_flour)) && Client_wallet >= w);
    }

    private static boolean Start_evalConditionFor(int fct) {
        switch(fct) {
          case 1: return begin_cond(begin_h);
          default: return false;
        }
    }

    private static boolean Run_evalConditionFor(int fct) {
        switch(fct) {
          case 1: return send_cond(send_sh);
          case 2: return buy_cond(buy_w);
          default: return false;
        }
    }

}