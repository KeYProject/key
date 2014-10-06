// This file is part of KeY - Integrated Deductive Software Design
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2014 Karlsruhe Institute of Technology, Germany
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General
// Public License. See LICENSE.TXT for details.
//

package de.uka.ilkd.key.util;

/**
 * Contains commonly (at least in the context of KeY) used Unicode symbols.
 * The names for the constants mostly derive from the common names in LaTeX,
 * such as the bottom symbol is noted as "BOT".
 * Some symbols are however referred to by their common name within KeY,
 * such as the equivalence arrow (aka. left-right arrow) is named "EQV".
 * In doubt, it is not a bad idea to give several names.
 * See <a href="http://www.fileformat.info/info/unicode/category/Sm/list.htm">
 * this list</a> for more symbols.
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
    public static final char NEQ = '\u2260';

    // temporal operators
    public static final char BOX = '\u25A1';
    public static final char DIAMOND = '\u25C7';
    public static final char CIRC = '\u2218';
    public static final char BULLET = '\u2219';

    // arithmetic stuff
    public static final char LEQ = '\u2264';
    public static final char GEQ = '\u2265';
    public static final char SUM = '\u2211';
    public static final char PROD = '\u220F';

    // sets
    public static final char IN = '\u220A';
    public static final char EMPTY = '\u2205';
    public static final char UNION = '\u222A';
    public static final char INTERSECT = '\u2229';
    public static final char SUBSET = '\u2286';
    public static final char SETMINUS = '\u2216';
    public static final char NATURALS = '\u2115';
    public static final char INTEGERS = '\u2124';

    // delimiters (for modalities)
    public static final char LANGLE = '\u27E8';
    public static final char RANGLE = '\u27E9';
    public static final char LLBRACKET = '\u27E6';
    public static final char RRBRACKET = '\u27E7';

    // sequences
    public static final char SEQ_SINGLETON_L = '\u2329';
    public static final char SEQ_SINGLETON_R = '\u232A';
    public static final char SEQ_CONCAT = '\u2218';

    // greek alphabet
    public static final char ALPHA = '\u03B1';
    public static final char BETA = '\u03B2';
    public static final char GAMMA = '\u03B3';
    public static final char DELTA = '\u03B4';
    public static final char EPSILON = '\u03B5';
    public static final char ZETA = '\u03B6';
    public static final char ETA = '\u03B7';
    public static final char THETA = '\u03B8';
    public static final char IOTA = '\u03B9';
    public static final char KAPPA = '\u03BA';
    public static final char LAMBDA = '\u03BB';
    public static final char MU = '\u03BC';
    public static final char NU = '\u03BD';
    public static final char XI = '\u03BE';
    public static final char OMICRON = '\u03BF';
    public static final char PI = '\u03C0';
    public static final char RHO = '\u03C1';
    public static final char SIGMA = '\u03C3';
    public static final char TAU = '\u03C4';
    public static final char UPSILON = '\u03C5';
    public static final char PHI = '\u03C6';
    public static final char CHI = '\u03C7';
    public static final char PSI = '\u03C8';
    public static final char OMEGA = '\u03C9';


    // also quite popular
    public static final char TOP = '\u22A4';
    public static final char BOT = '\u22A5';
    public static final char TURNSTILE = '\u22A6';
    public static final char MODELS = '\u22A7';
    public static final char PRECEDES = '\u227A';


    // non-logic symbols
    public static final char COPYRIGHT = '\u00A9';
    public static final char ENSPACE = '\u2002';
    public static final char EMSPACE = '\u2003';
    public static final char ENDASH = '\u2013';
    public static final char FLQQ = '\u00ab';
    public static final char FRQQ = '\u00bb';


    /**
     * Return a String containing em-spaces.
     */
    public static String emSpaces (int em) {
        final StringBuffer sb = new StringBuffer();
        for (int i= 0; i < em; i++)
            sb.append(EMSPACE);
        return sb.toString();
    }


    /** For testing Unicode symbols. */
//    public static void main(String[] args){
//        System.out.println("Testing Unicode symbols:");
//        for (java.lang.reflect.Field f: UnicodeHelper.class.getDeclaredFields()){
//            try {
//                System.out.print(f.get(null));
//            } catch (Exception e) {
//                System.out.println("Error in Unicode test.");
//                e.printStackTrace();
//            }
//        }
//    }

}