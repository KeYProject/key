//import java.util.Random;
public class BikeRental {
    //    private static Random random = new Random();
    //@ public ghost final static int Inactive = 0;
    //@ public ghost final static int Payment = 1;
    //@ public ghost final static int Using = 2;
    //@ public ghost final static int Return = 3;
    //@ public ghost final static int EndNoDispute = 4;
    //@ public ghost final static int Dispute = 5;
    //@ public ghost final static int End = 6;
    //@ public invariant -1 <= currentState < 7;
    //@ public ghost static int currentState = -1;
    //@ public static invariant wallet >= 0;
    public static int wallet;
    //@ public static invariant Lender_wallet >= 0;
    public static int Lender_wallet;
    //@ public static invariant Borrower_wallet >= 0;
    public static int Borrower_wallet;
    //@ public static invariant Authority_wallet >= 0;
    public static int Authority_wallet;

    public static int Lender;
    public static int Borrower;
    public static int Authority;

    public static int cost;
    //@ public static invariant rentingTime >= 0;
    public static int rentingTime;
    public static int code;
    //@ public static invariant now >= 0;
    public static int now = 0;
    //@ public static invariant DT_MIN.length == 1;
    //@ public static invariant DT_MAX.length == DT_MIN.length && DT_MIN != DT_MAX;
    //@ public static invariant (\forall int i; 0 <= i < DT_MIN.length; DT_MIN[i] <= DT_MAX[i]);
    public static int[] DT_MIN = new int[1];
    public static int[] DT_MAX = new int[1];

    // create unique name by prefixing function name tp parameter name
    public static int offer_x;
    public static int pay_h;

    // create unique name by prefixing function name tp parameter name
    public static int disputeL1_x;
    // create unique name by prefixing function name tp parameter name
    public static int disputeL2_x;
    // create unique name by prefixing function name tp parameter name
    public static int disputeB1_x;
    // create unique name by prefixing function name tp parameter name
    public static int disputeB2_x;
    // create unique name by prefixing function name tp parameter name
    public static int verdict_x, verdict_y;
    //@ public static invariant ( rentingTime > 0 && cost >= 0 );
    /*@ model two_state static boolean assetPreservation() {
            return wallet + Lender_wallet + Borrower_wallet + Authority_wallet == \old(wallet + Lender_wallet + Borrower_wallet + Authority_wallet);
     } */
    // functions of the stipula contract
    /*@ public normal_behavior
      @ requires (true);
      @ assignable code;
      @ ensures code == x;
      @ ensures assetPreservation();
      @*/
    public static void offer(int x) {
        code = x;
    }
    /*@ public normal_behavior
      @ requires ((h == cost) && Borrower_wallet >= h);
      @ requires h >= 0 && Borrower_wallet >= h;
      @ assignable wallet, Borrower_wallet, DT_MIN[0], DT_MAX[0];
      @ ensures wallet == \old(wallet + h) && Borrower_wallet == \old(Borrower_wallet - h);
      @ ensures  ( \old(DT_MIN[0] == -1 && DT_MAX[0] == -1) ?
      @            DT_MIN[0] == now + rentingTime && DT_MAX[0] == now + rentingTime
      @            : (
      @                ( DT_MAX[0] == (now + rentingTime > \old(DT_MAX[0]) ?
      @                                            now + rentingTime :  \old(DT_MAX[0])))
      @                && DT_MIN[0] == \old(DT_MIN[0])
      @              )
      @          );
      @ ensures assetPreservation();
      @*/
    public static void pay(int h) {
        int tmp_0 = h; Borrower_wallet = Borrower_wallet - tmp_0;wallet = wallet + tmp_0; // asset transfer

        int new_time;
        new_time = now + rentingTime;
        if (DT_MIN[0] == -1 && DT_MAX[0] == -1) {
            DT_MIN[0] = new_time;
            DT_MAX[0] = new_time;
        } else if (DT_MAX[0] < new_time) {
            DT_MAX[0] = new_time;
        }
    }
    /*@ public normal_behavior
      @ requires (true);
      @ assignable \nothing;
      @ ensures true;
      @ ensures assetPreservation();
      @*/
    public static void end() {

    }
    /*@ public normal_behavior
      @ requires (true);
      @ requires wallet >= wallet;
      @ assignable wallet, Lender_wallet;
      @ ensures wallet == 0 && Lender_wallet == \old(Lender_wallet + wallet);
      @ ensures assetPreservation();
      @*/
    public static void rentalOk() {
        int tmp_1 = wallet; wallet = wallet - tmp_1;Lender_wallet = Lender_wallet + tmp_1; // asset transfer
    }
    /*@ public normal_behavior
      @ requires (true);
      @ assignable \nothing;
      @ ensures true;
      @ ensures assetPreservation();
      @*/
    public static void disputeL1(int x) {

    }
    /*@ public normal_behavior
      @ requires (true);
      @ assignable \nothing;
      @ ensures true;
      @ ensures assetPreservation();
      @*/
    public static void disputeL2(int x) {

    }
    /*@ public normal_behavior
      @ requires (true);
      @ assignable \nothing;
      @ ensures true;
      @ ensures assetPreservation();
      @*/
    public static void disputeB1(int x) {

    }
    /*@ public normal_behavior
      @ requires (true);
      @ assignable \nothing;
      @ ensures true;
      @ ensures assetPreservation();
      @*/
    public static void disputeB2(int x) {

    }
    /*@ public normal_behavior
      @ requires (((y >= 0) && (y <= 1)));
      @ requires wallet >= (y * wallet) && wallet >= wallet;
      @ assignable wallet, Lender_wallet, Borrower_wallet;
      @ ensures wallet == 0 && Lender_wallet == \old(Lender_wallet + (y * wallet)) && Borrower_wallet == \old(Borrower_wallet + (wallet - (y * wallet)));
      @ ensures assetPreservation();
      @*/
    public static void verdict(int x, int y) {


        int tmp_2 = (y * wallet); wallet = wallet - tmp_2;Lender_wallet = Lender_wallet + tmp_2; // asset transfer
        int tmp_3 = wallet; wallet = wallet - tmp_3;Borrower_wallet = Borrower_wallet + tmp_3; // asset transfer
    }
    // event functions
    /*@ public normal_behavior
      @ assignable \nothing;
      @ ensures true;
      @ ensures true;
      @ ensures assetPreservation();
      @*/
    public static void event_0() {

    }
    // behavior
    /*@ public normal_behavior
      @ requires ( Borrower_wallet >= cost && wallet == 0 );
      @ ensures  ( currentState == EndNoDispute ==> (wallet == 0 && Lender_wallet == \old(Lender_wallet) + (\old(Borrower_wallet) -  Borrower_wallet)) );
      @ assignable \everything;
      @*/
    public static void behavior() {
        //@ set currentState = -1;
        resetDispatch();
        GenInactive();
    }

    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenInactive() {
        //@ set currentState = Inactive;
        int next_action = computeNextStepEmptyEvents(1);
        switch (next_action) {
            case 1:
                offer(offer_x);
                GenPayment();
                break;
            default: break;
        }
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenPayment() {
        //@ set currentState = Payment;
        int next_action = computeNextStepEmptyEvents(1);
        //@ assume next_action < 0 || (next_action > 0 ? Payment_evalConditionFor(next_action) : false);
        switch (next_action) {
            case 1:
                pay(pay_h);
                GenUsing();
                break;
            default: break;
        }
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenUsing() {
        //@ set currentState = Using;
        int next_action = computeNextStep(3, new int[] { 0 });
        switch (next_action) {
            case 1:
                end();
                GenReturn();
                break;
            case 2:
                disputeL1(disputeL1_x);
                GenDispute();
                break;
            case 3:
                disputeB1(disputeB1_x);
                GenDispute();
                break;
            case -1:
                event_0();
                DT_MIN[0] = -1;
                DT_MAX[0] = -1;
                GenReturn();
                break;
            default: break;
        }
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenReturn() {
        //@ set currentState = Return;
        int next_action = computeNextStepEmptyEvents(3);
        switch (next_action) {
            case 1:
                rentalOk();
                GenEndNoDispute();
                break;
            case 2:
                disputeL2(disputeL2_x);
                GenDispute();
                break;
            case 3:
                disputeB2(disputeB2_x);
                GenDispute();
                break;
            default: break;
        }
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenEndNoDispute() {
        //@ set currentState = EndNoDispute;
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenDispute() {
        //@ set currentState = Dispute;
        int next_action = computeNextStepEmptyEvents(1);
        //@ assume next_action < 0 || (next_action > 0 ? Dispute_evalConditionFor(next_action) : false);
        switch (next_action) {
            case 1:
                verdict(verdict_x, verdict_y);
                GenEnd();
                break;
            default: break;
        }
    }
    // GEN_C(Q) for state that does not occur on a cycle
    public static void GenEnd() {
        //@ set currentState = End;
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
      @ requires true;
      @ requires -1 <= lower <= upper;
      @ ensures lower <= \result <= upper;
      @ assignable \nothing;
     */
    private /*@ helper @*/ static int choose(int lower, int upper) {
        return lower;
//return random.nextInt(upper + 1 - lower) + lower;
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

    private static boolean pay_cond(int h) {
        return ((h == cost) && Borrower_wallet >= h);
    }




    private static boolean verdict_cond(int x, int y) {
        return (((y >= 0) && (y <= 1)));
    }

    private static boolean Inactive_evalConditionFor(int fct) {
        return true;
    }

    private static boolean Payment_evalConditionFor(int fct) {
        switch(fct) {
            case 1: return pay_cond(pay_h);
            default: return false;
        }
    }

    private static boolean Using_evalConditionFor(int fct) {
        return true;
    }

    private static boolean Return_evalConditionFor(int fct) {
        return true;
    }


    private static boolean Dispute_evalConditionFor(int fct) {
        switch(fct) {
            case 1: return verdict_cond(verdict_x, verdict_y);
            default: return false;
        }
    }

}