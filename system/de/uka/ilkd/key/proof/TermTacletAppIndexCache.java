// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//


package de.uka.ilkd.key.proof;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.rule.FindTaclet;
import de.uka.ilkd.key.rule.Taclet;

/**
 * Cache that is used for accelerating <code>TermTacletAppIndex</code>.
 * Basically, this is a mapping from terms to objects of
 * <code>TermTacletAppIndex</code>, following the idea that the same taclets
 * will be applicable to an occurrence of the same term in different places. 
 */
public class TermTacletAppIndexCache {

//    private int hits = 0, total = 0;
    
    private final TwoStageCache antecCache, succCache, rewriteCache;
    
    private TermTacletAppIndexCache(TwoStageCache antecCache,
                                    TwoStageCache succCache,
                                    TwoStageCache rewriteCache) {
        this.antecCache = antecCache;
        this.succCache = succCache;
        this.rewriteCache = rewriteCache;
    }
    
    public TermTacletAppIndexCache() {
        this ( new TwoStageCache (), new TwoStageCache (), new TwoStageCache () );
    }
        
    private TwoStageCache getCache(PosInOccurrence pos) {
        if ( pos.isTopLevel () ) {
            if ( pos.isInAntec () )
                return antecCache;
            else
                return succCache;
        } else
            return rewriteCache;
    }
    
    public TermTacletAppIndex getIndexForTerm(PosInOccurrence pos) {
        final TermTacletAppIndex res =
            (TermTacletAppIndex)getCache ( pos ).get ( pos.subTerm () );
        
//        countAccess ( res != null );

        return res;
    }

//    private void countAccess(boolean hit) {
//        ++total;
//        if ( hit ) ++hits;
//        if (total % 1000 == 0 && total != 0) {
//            System.out.println("" + ((double)hits)/(double)total + " " + hashCode());
//        }
//    }

    public void putIndexForTerm(PosInOccurrence pos, TermTacletAppIndex index) {
        getCache ( pos ).put ( pos.subTerm(), index );
    }

    public boolean isRelevantTaclet (Taclet t) {
        return t instanceof FindTaclet;
    }
    
    private static class TwoStageCache {
        private final static int SIZE = 1000;
        
        private Map primary = new HashMap ();
        private Map secondary = new HashMap ();
        
        public void put(Object key, Object value) {
            if ( primary.size () >= SIZE ) {
                secondary.clear ();
                final Map t = secondary;
                secondary = primary;
                primary = t;
            }
            
            primary.put ( key, value );
        }

        public Object get(Object key) {
            Object value = primary.get ( key );
            if ( value != null ) return value;

            value = secondary.get ( key );
            if ( value == null ) return null;
            
            put ( key, value );
            return value;
        }
    }
}
