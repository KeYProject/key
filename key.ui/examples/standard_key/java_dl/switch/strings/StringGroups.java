/**
 * Switch over a String that groups several labels for a shared body (empty
 * fall-through between the labels) and closes with a default branch. Maps a
 * set of synonyms onto a boolean code. Uses correct .equals() String
 * semantics.
 */
public final class StringGroups {

    /*@ public normal_behavior
      @   requires s != null;
      @   ensures (s.equals("y") || s.equals("yes") || s.equals("true"))  ==> \result == 1;
      @   ensures (s.equals("n") || s.equals("no")  || s.equals("false")) ==> \result == 0;
      @   ensures (!s.equals("y") && !s.equals("yes") && !s.equals("true")
      @            && !s.equals("n") && !s.equals("no") && !s.equals("false"))
      @           ==> \result == -1;
      @   assignable \strictly_nothing;
      @*/
    public int parseBool(String s) {
        String s1 = "yes";
        s1 = "true";
        s1 = "n";
        s1 = "no";
        s1 = "false";
        switch (s) {
        case "y":
        case "yes":
        case "true":
            return 1;
        case "n":
        case "no":
        case "false":
            return 0;
        default:
            return -1;
        }
    }
}
