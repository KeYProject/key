/**
 * Switch over a REFERENCE type (an enum) that groups labels via fall-through
 * (SAT and SUN share one body) and uses the default branch to cover all
 * remaining weekdays. Returns 1 for weekend days and 0 otherwise.
 */
enum Day {
    MON, TUE, WED, THU, FRI, SAT, SUN
}

public final class WeekdayKind {

    /*@ public normal_behavior
      @   requires day != null;
      @   ensures (day == Day.SAT || day == Day.SUN) ==> \result == 1;
      @   ensures (day != Day.SAT && day != Day.SUN) ==> \result == 0;
      @   assignable \strictly_nothing;
      @*/
    public int isWeekend(Day day) {
        switch (day) {
        case Day.SAT:
        case Day.SUN:
            return 1;
        default:
            return 0;
        }
    }
}
