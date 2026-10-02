import java.util.Random;
public class Bet {
    private static Random random = new Random();
    public final static int Init = 0;
    public final static int First = 1;
    public final static int Fail = 2;
    public final static int Run = 3;
    public final static int End = 4;
    //@ public invariant -1 <= currentState < 5;
    public static int currentState = -1;
    //@ public static invariant wallet1 >= 0;
    public static int wallet1;
    //@ public static invariant Better1_wallet1 >= 0;
    public static int Better1_wallet1;
    //@ public static invariant Better2_wallet1 >= 0;
    public static int Better2_wallet1;
    //@ public static invariant DataProvider_wallet1 >= 0;
    public static int DataProvider_wallet1;
    //@ public static invariant wallet2 >= 0;
    public static int wallet2;
    //@ public static invariant Better1_wallet2 >= 0;
    public static int Better1_wallet2;
    //@ public static invariant Better2_wallet2 >= 0;
    public static int Better2_wallet2;
    //@ public static invariant DataProvider_wallet2 >= 0;
    public static int DataProvider_wallet2;

    public static int Better1;
    public static int Better2;
    public static int DataProvider;

    public static int val1;
    public static int val2;
    public static int event;
    public static int amount;
    //@ public static invariant t_before >= 0;
    public static int t_before;
    //@ public static invariant t_after >= 0;
    public static int t_after;
    //@ public static invariant now >= 0;
    public static int now = 0;
    //@ public static invariant DT_MIN.length == 2;
    //@ public static invariant DT_MAX.length == DT_MIN.length && DT_MIN != DT_MAX;
    //@ public static invariant (\forall int i; 0 <= i < DT_MIN.length; DT_MIN[i] <= DT_MAX[i]);
    public static int[] DT_MIN = new int[2];
    public static int[] DT_MAX = new int[2];

  // create unique name by prefixing function name tp parameter name
    public static int place_bet_x;
    public static int place_bet_h;
  // create unique name by prefixing function name tp parameter name
    public static int place_bet2_x;
    public static int place_bet2_h;
  // create unique name by prefixing function name tp parameter name
    public static int data_x, data_z;
   //@ public static invariant ( 0 <= t_before < t_after && amount > 0 );
    /*@ model two_state static boolean assetPreservation() {
            return wallet1 + Better1_wallet1 + Better2_wallet1 + DataProvider_wallet1 == \old(wallet1 + Better1_wallet1 + Better2_wallet1 + DataProvider_wallet1) && wallet2 + Better1_wallet2 + Better2_wallet2 + DataProvider_wallet2 == \old(wallet2 + Better1_wallet2 + Better2_wallet2 + DataProvider_wallet2);
     } */
    // functions of the stipula contract
    /*@ public normal_behavior
      @ requires ((h == amount) && Better1_wallet1 >= h);
      @ requires h >= 0 && Better1_wallet1 >= h;
      @ assignable wallet1, val1, Better1_wallet1, DT_MIN[0], DT_MAX[0];
      @ ensures wallet1 == \old(wallet1 + h) && val1 == x && Better1_wallet1 == \old(Better1_wallet1 - h);
      @ ensures  ( \old(DT_MIN[0] == -1 && DT_MAX[0] == -1) ?
      @            DT_MIN[0] == now + t_before && DT_MAX[0] == now + t_before
      @            : (
      @                ( DT_MAX[0] == (now + t_before > \old(DT_MAX[0]) ?
      @                                            now + t_before :  \old(DT_MAX[0])))
      @                && DT_MIN[0] == \old(DT_MIN[0])
      @              )
      @          );
      @ ensures assetPreservation();
      @*/
    public static void place_bet(int x, int h) {
        int tmp_0 = h; Better1_wallet1 = Better1_wallet1 - tmp_0;wallet1 = wallet1 + tmp_0; // asset transfer
        val1 = x;
      int new_time;
      new_time = now + t_before;
      if (DT_MIN[0] == -1 && DT_MAX[0] == -1) {
          DT_MIN[0] = new_time;
          DT_MAX[0] = new_time;
      } else if (DT_MAX[0] < new_time) {
          DT_MAX[0] = new_time;
      }
    }
    /*@ public normal_behavior
      @ requires ((h == amount) && Better2_wallet2 >= h);
      @ requires h >= 0 && Better2_wallet2 >= h;
      @ assignable wallet2, val2, Better2_wallet2, DT_MIN[1], DT_MAX[1];
      @ ensures wallet2 == \old(wallet2 + h) && val2 == x && Better2_wallet2 == \old(Better2_wallet2 - h);
      @ ensures  ( \old(DT_MIN[1] == -1 && DT_MAX[1] == -1) ?
      @            DT_MIN[1] == now + t_after && DT_MAX[1] == now + t_after
      @            : (
      @                ( DT_MAX[1] == (now + t_after > \old(DT_MAX[1]) ?
      @                                            now + t_after :  \old(DT_MAX[1])))
      @                && DT_MIN[1] == \old(DT_MIN[1])
      @              )
      @          );
      @ ensures assetPreservation();
      @*/
    public static void place_bet2(int x, int h) {
        int tmp_1 = h; Better2_wallet2 = Better2_wallet2 - tmp_1;wallet2 = wallet2 + tmp_1; // asset transfer
        val2 = x;
      int new_time;
      new_time = now + t_after;
      if (DT_MIN[1] == -1 && DT_MAX[1] == -1) {
          DT_MIN[1] = new_time;
          DT_MAX[1] = new_time;
      } else if (DT_MAX[1] < new_time) {
          DT_MAX[1] = new_time;
      }
    }
    /*@ public normal_behavior
      @ requires ((x == event));
      @ assignable wallet2, wallet1, Better1_wallet2, Better1_wallet1, Better2_wallet1, DataProvider_wallet1, DataProvider_wallet2, Better2_wallet2;
      @ ensures wallet2 == \old(((z == val1) && (z == val2)) ? 0 : (((z == val1) && (z != val2)) ? 0 : (((z != val1) && (z == val2)) ? 0 : 0))) && wallet1 == \old(((z == val1) && (z == val2)) ? 0 : (((z == val1) && (z != val2)) ? 0 : (((z != val1) && (z == val2)) ? 0 : 0))) && Better1_wallet2 == \old(((z == val1) && (z == val2)) ? Better1_wallet2 : (((z == val1) && (z != val2)) ? (Better1_wallet2 + wallet2) : Better1_wallet2)) && Better1_wallet1 == \old(((z == val1) && (z == val2)) ? (Better1_wallet1 + wallet1) : (((z == val1) && (z != val2)) ? (Better1_wallet1 + wallet1) : Better1_wallet1)) && Better2_wallet1 == \old(((z == val1) && (z == val2)) ? Better2_wallet1 : (((z == val1) && (z != val2)) ? Better2_wallet1 : (((z != val1) && (z == val2)) ? (Better2_wallet1 + wallet1) : Better2_wallet1))) && DataProvider_wallet1 == \old(((z == val1) && (z == val2)) ? DataProvider_wallet1 : (((z == val1) && (z != val2)) ? DataProvider_wallet1 : (((z != val1) && (z == val2)) ? DataProvider_wallet1 : (DataProvider_wallet1 + wallet1)))) && DataProvider_wallet2 == \old(((z == val1) && (z == val2)) ? DataProvider_wallet2 : (((z == val1) && (z != val2)) ? DataProvider_wallet2 : (((z != val1) && (z == val2)) ? DataProvider_wallet2 : (DataProvider_wallet2 + wallet2)))) && Better2_wallet2 == \old(((z == val1) && (z == val2)) ? (Better2_wallet2 + wallet2) : (((z == val1) && (z != val2)) ? Better2_wallet2 : (((z != val1) && (z == val2)) ? (Better2_wallet2 + wallet2) : Better2_wallet2)));
      @ ensures assetPreservation();
      @*/
    public static void data(int x, int z) {
        if (((z == val1) && (z == val2))) {
		 int tmp_2 = wallet1; wallet1 = wallet1 - tmp_2;Better1_wallet1 = Better1_wallet1 + tmp_2; // asset transfer
int tmp_3 = wallet2; wallet2 = wallet2 - tmp_3;Better2_wallet2 = Better2_wallet2 + tmp_3; // asset transfer
		} else {
		if (((z == val1) && (z != val2))) {
		 int tmp_4 = wallet2; wallet2 = wallet2 - tmp_4;Better1_wallet2 = Better1_wallet2 + tmp_4; // asset transfer
int tmp_5 = wallet1; wallet1 = wallet1 - tmp_5;Better1_wallet1 = Better1_wallet1 + tmp_5; // asset transfer
		} else {
		if (((z != val1) && (z == val2))) {
		 int tmp_6 = wallet1; wallet1 = wallet1 - tmp_6;Better2_wallet1 = Better2_wallet1 + tmp_6; // asset transfer
int tmp_7 = wallet2; wallet2 = wallet2 - tmp_7;Better2_wallet2 = Better2_wallet2 + tmp_7; // asset transfer
		} else {
		int tmp_8 = wallet2; wallet2 = wallet2 - tmp_8;DataProvider_wallet2 = DataProvider_wallet2 + tmp_8; // asset transfer
int tmp_9 = wallet1; wallet1 = wallet1 - tmp_9;DataProvider_wallet1 = DataProvider_wallet1 + tmp_9; // asset transfer
		}
		}
		}
    }
    // event functions
    /*@ public normal_behavior
      @ requires wallet1 >= wallet1;
      @ assignable wallet1, Better1_wallet1;
      @ ensures wallet1 == 0 && Better1_wallet1 == \old(Better1_wallet1 + wallet1);
      @ ensures wallet1 == 0 && Better1_wallet1 == \old(Better1_wallet1 + wallet1);
      @ ensures assetPreservation();
      @*/
    public static void event_0() {
        int tmp_10 = wallet1; wallet1 = wallet1 - tmp_10;Better1_wallet1 = Better1_wallet1 + tmp_10; // asset transfer
    }
    /*@ public normal_behavior
      @ requires wallet1 >= wallet1 && wallet2 >= wallet2;
      @ assignable wallet2, wallet1, Better1_wallet1, Better2_wallet2;
      @ ensures wallet2 == 0 && wallet1 == 0 && Better1_wallet1 == \old(Better1_wallet1 + wallet1) && Better2_wallet2 == \old(Better2_wallet2 + wallet2);
      @ ensures wallet2 == 0 && wallet1 == 0 && Better1_wallet1 == \old(Better1_wallet1 + wallet1) && Better2_wallet2 == \old(Better2_wallet2 + wallet2);
      @ ensures assetPreservation();
      @*/
    public static void event_1() {
        int tmp_11 = wallet1; wallet1 = wallet1 - tmp_11;Better1_wallet1 = Better1_wallet1 + tmp_11; // asset transfer
        int tmp_12 = wallet2; wallet2 = wallet2 - tmp_12;Better2_wallet2 = Better2_wallet2 + tmp_12; // asset transfer
    }
    // behavior
    /*@ public normal_behavior
      @ requires ( wallet1 == 0 && wallet2 == 0 );
      @ ensures  ( assetPreservation() ) && ( currentState == Fail ==> (wallet1 == 0 && wallet2 == 0 && Better1_wallet1==\old(Better1_wallet1) && Better1_wallet2==\old(Better1_wallet2) && Better2_wallet1==\old(Better2_wallet1) && Better2_wallet2==\old(Better2_wallet2)) );
      @ assignable \everything;
      @*/
    public static void behavior() {
        currentState = -1;
        resetDispatch();
        GenInit();
    }

    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenInit() {
        currentState = Init;
        int next_action = computeNextStepEmptyEvents(1);
        //@ assume next_action < 0 || (next_action > 0 ? Init_evalConditionFor(next_action) : false);
        switch (next_action) {
          case 1:
            place_bet(place_bet_x, place_bet_h);
            GenFirst();
            break;
          default: break;
        }
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenFirst() {
        currentState = First;
        int next_action = computeNextStep(1, new int[] { 0 });
        //@ assume next_action < 0 || (next_action > 0 ? First_evalConditionFor(next_action) : false);
        switch (next_action) {
          case 1:
            place_bet2(place_bet2_x, place_bet2_h);
            GenRun();
            break;
          case -1:
            event_0();
            DT_MIN[0] = -1;
            DT_MAX[0] = -1;
            GenFail();
            break;
          default: break;
        }
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenFail() {
        currentState = Fail;
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenRun() {
        currentState = Run;
        int next_action = computeNextStep(1, new int[] { 1 });
        //@ assume next_action < 0 || (next_action > 0 ? Run_evalConditionFor(next_action) : false);
        switch (next_action) {
          case 1:
            data(data_x, data_z);
            GenEnd();
            break;
          case -2:
            event_1();
            DT_MIN[1] = -1;
            DT_MAX[1] = -1;
            GenFail();
            break;
          default: break;
        }
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
 
    private static boolean place_bet_cond(int x, int h) {
        return ((h == amount) && Better1_wallet1 >= h);
    }
 
    private static boolean place_bet2_cond(int x, int h) {
        return ((h == amount) && Better2_wallet2 >= h);
    }
 
    private static boolean data_cond(int x, int z) {
        return ((x == event));
    }

    private static boolean Init_evalConditionFor(int fct) {
        switch(fct) {
          case 1: return place_bet_cond(place_bet_x, place_bet_h);
          default: return false;
        }
    }

    private static boolean First_evalConditionFor(int fct) {
        switch(fct) {
          case 1: return place_bet2_cond(place_bet2_x, place_bet2_h);
          default: return false;
        }
    }


    private static boolean Run_evalConditionFor(int fct) {
        switch(fct) {
          case 1: return data_cond(data_x, data_z);
          default: return false;
        }
    }

}