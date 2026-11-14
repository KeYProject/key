/**
 * Example demonstrating Java 16+ instanceof pattern matching support in KeY.
 * 
 * This feature allows you to write:
 *   if (obj instanceof String s) {
 *       // s is automatically bound and can be used here
 *       return s.length();
 *   }
 * 
 * Instead of the traditional:
 *   if (obj instanceof String) {
 *       String s = (String) obj;
 *       return s.length();
 *   }
 */
public class InstanceOfPatternExample {

    /*@ normal_behavior
      @ requires obj != null;
      @ ensures \result instanceof String;
      @*/
    public static Object getString(Object obj) {
        return "ha";
    }

    /*@ normal_behavior
      @ requires obj != null;
      @ ensures true;
      @*/
    public static boolean testForNull(Object obj) {
        if( obj instanceof Object o) {
            //@ assert obj != null;
            //@ assert o != null;
            return true;
        }
        return false;
    }

    
    /*@ normal_behavior
      @ requires obj != null;
      @ ensures \result;
      @*/
    public static boolean isString(Object obj) {
        return getString(obj) instanceof String id && id.length() >= 0;
    }

    /*@ normal_behavior
      @ requires obj instanceof String;
      @ ensures \result >= 0;
      @*/
    public static int getStringLength(Object obj) {
        if (obj instanceof String s) {
            // Pattern variable 's' is bound and has type String here
            //@ assert s != null;
            return s.length();
        }
        return -1;
    }
    
    /**
     * Negated instanceof pattern - note that the binding only happens
     * in the else branch, not the if branch.
     */
    /*@ normal_behavior
      @ requires true;
      @ ensures \result >= 0;
      @*/
    public static int checkNotString(Object obj) {
        Object a = new Object();
        //@ assert a != null;
        if (!(obj instanceof String s)) {
            // 's' is NOT bound here
            return 0;
        } else {
            // 's' IS bound here (in the else branch)
            //@ assert s != null;
            return s.length();
        }
    }
    
    /**
     * Multiple instanceof patterns in sequence.
     */
    /*@ normal_behavior
      @ requires \invariant_for(obj);
      @ ensures true;
      @*/
    public static int processNumber(Object obj) {
        if (obj instanceof Integer i) {
            return i.intValue();
        } else if (obj instanceof Double d) {
            //@ assert d != null;
            return 1;
        } else if (obj instanceof Long l) {
            //@ assert l != null;
            return 2;
        }
        return -1;
    }
    
    /**
     * Pattern matching with method calls.
     */
    /*@ normal_behavior
      @ requires \invariant_for(obj);
      @ ensures \result >= -1;
      @*/
    public static int getToStringLength(Object obj) {
        if (obj instanceof String s) {
            // Can call methods on the pattern variable
            return s.toString().length();
        }
        return -1;
    }
    
//    /**
//     * Pattern matching in complex expressions.
//     */
//    /*@ normal_behavior
//      @ requires obj1 != null && obj2 != null;
//      @ ensures \result == 0 || \result > 0;
//      @*/
//    public static int compareIfBothStrings(Object obj1, Object obj2) {
//        if (obj1 instanceof String s1 && obj2 instanceof String s2) {
//            // Both s1 and s2 are bound in this branch
//            //@ assert s1 != null && s2 != null;
//            return s1.compareTo(s2);
//        }
//        return 0;
//    }
    
    /**
     * Traditional instanceof vs pattern matching.
     * This shows both styles for comparison.
     */
    /*@ normal_behavior
      @ requires true;
      @ ensures \result >= -1;
      @*/
    public static int traditionalVsPattern(Object obj) {
        // Traditional style (still supported)
        if (obj instanceof String) {
            String s = (String) obj;
            int traditional = s.length();
            
            // Pattern matching style (more concise)
            if (obj instanceof String pattern) {
                int patternStyle = pattern.length();
                //@ assert traditional == patternStyle;
            }
            
            return traditional;
        }
        return -1;
    }
    
    /**
     * Pattern matching in a while loop: the variable is bound in the body.
     */
    /*@ normal_behavior
      @ requires true;
      @ ensures \result >= 0;
      @*/
    public static int whilePattern(Object obj) {
        int n = 0;
        while (obj instanceof String s) {
            n += s.length();
            obj = null;
        }
        return n;
    }

    /**
     * Pattern matching after a loop: the variable is bound after the loop exits normally.
     */
    /*@ normal_behavior
      @ requires true;
      @ ensures \result >= 0;
      @*/
    public static int afterLoopPattern() {
        Object obj = new String("x");
        while (!(obj instanceof String s)) {
            obj = null;
        }
        return s.length();
    }

    /**
     * Main method for testing.
     */
    public static void main(String[] args) {
        System.out.println(getStringLength("Hello"));  // 5
        System.out.println(getStringLength(42));       // -1
        
        System.out.println(checkNotString(42));        // 0
        System.out.println(checkNotString("World"));   // 5
        
        System.out.println(processNumber(42));         // 42
        System.out.println(processNumber(3.14));       // 1
        System.out.println(processNumber(100L));       // 2
        
        System.out.println(getToStringLength("Test")); // 4
    }
}
