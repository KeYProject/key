package de.uka.ilkd.key.util;

/**
 * Contains commonly (at least in the context of KeY) used Unicode symbols.
 * The names for the constants mostly derive from the common names in LaTeX,
 * such as the bottom symbol is noted as "BOT".
 * Some symbols are however refered to by their common name within KeY,
 * such as the equivalence arrow (aka. left-right arrow) is named "EQV".
 * In doubt, it is not a bad idea to give several names.
 * @author bruns
 *
 */
public final class UnicodeHelper {
    
    // first order operators
    public static final char NEG = '\u00AC';
    public static final char IMP = '\u2192';
    public static final char EQV = '\u2194';
    public static final char FORALL = '\u2200';
    public static final char EXISTS = '\u2203';
    public static final char AND = '\u2227';
    public static final char OR = '\u2228'; 

    // temporal operators
    public static final char BOX = '\u25A1';
    public static final char DIAMOND = '\u25C7';
    public static final char CIRC = '\u2218';
    public static final char BULLET = '\u2219';
    
    // arithmetic stuff
    public static final char LEQ = '\u2264';
    public static final char GEQ = '\u2265';
    
    // sets
    public static final char IN = '\u220A'; // aka. contains
    public static final char EMPTY = '\u2205';
    public static final char UNION = '\u222A';
    public static final char INTERSECT = '\u2229';
    public static final char SUBSET = '\u2286';
    public static final char SETMINUS = '\u2216';
    public static final char INTEGERS = '\u2124';
    
    // also quite popular
    public static final char TOP = '\u22A4';
    public static final char BOT = '\u22A5';
    public static final char TURNSTILE = '\u22A6';
    public static final char MODELS = '\u22A7';
    
    
    
}