/**
 * Switch over a REFERENCE type (an enum) with the default branch last and no
 * fall-through. KeY inserts a null check for the switch selector, hence the
 * "requires light != null" precondition.
 *
 * Note: KeY expects enum case labels in qualified form
 * ("case Light.RED:" rather than "case RED:").
 */
enum Light {
    RED, YELLOW, GREEN
}

public final class TrafficLight {

    /*@ public normal_behavior
      @   requires light != null;
      @   // Stated as one ordered conditional rather than three separate
      @   // "light == X ==> \result == k" clauses: that form would require
      @   // proving the enum constants pairwise distinct (a manual step),
      @   // whereas the ordered form is discharged automatically.
      @   ensures \result == (light == Light.RED    ? 0
      @                     : light == Light.YELLOW ? 1
      @                     : light == Light.GREEN  ? 2 : -1);
      @   assignable \strictly_nothing;
      @*/
    public int code(Light light) {
        switch (light) {
        case Light.RED:
            return 0;
        case Light.YELLOW:
            return 1;
        case Light.GREEN:
            return 2;
        default:
            return -1;
        }
    }
}
