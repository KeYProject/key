// This file is part of KeY - Integrated Deductive Software Design 
//
// Copyright (C) 2001-2011 Universitaet Karlsruhe (TH), Germany 
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
// Copyright (C) 2011-2013 Karlsruhe Institute of Technology, Germany 
//                         Technical University Darmstadt, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General 
// Public License. See LICENSE.TXT for details.
// 


/** tests the TacletIndex class.*/
package de.uka.ilkd.key.proof;

import java.util.Map;

import junit.framework.TestCase;
import de.uka.ilkd.key.collection.ImmutableList;
import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.java.ServiceCaches;
import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.logic.SequentFormula;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.PosInTerm;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.ITermTacletAppIndexCache;
import de.uka.ilkd.key.proof.NullNewRuleListener;
import de.uka.ilkd.key.proof.TacletIndex;
import de.uka.ilkd.key.proof.TermTacletAppIndex;
import de.uka.ilkd.key.proof.TermTacletAppIndexCacheSet;
import de.uka.ilkd.key.proof.PrefixTermTacletAppIndexCacheImpl.CacheKey;
import de.uka.ilkd.key.proof.rulefilter.SetRuleFilter;
import de.uka.ilkd.key.proof.rulefilter.TacletFilter;
import de.uka.ilkd.key.rule.NoPosTacletApp;
import de.uka.ilkd.key.rule.Taclet;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.util.LRUCache;


public class TestTermTacletAppIndex extends TestCase{   

    NoPosTacletApp ruleRewriteNonH1H2; 
    NoPosTacletApp ruleNoFindNonH1H2H3;
    NoPosTacletApp ruleAntecH1;
    NoPosTacletApp ruleSucc;
    NoPosTacletApp ruleMisMatch;
    NoPosTacletApp notfreeconflict;
    NoPosTacletApp remove_f;
    NoPosTacletApp remove_ff;
    NoPosTacletApp remove_zero;
        
    public TestTermTacletAppIndex(String name) {
	super(name);
    }

    private Taclet taclet(String name) {
	return TacletForTests.getTaclet(name).taclet();
    }
    
    public void setUp() {
        TacletForTests.parse(System.getProperty("key.home")+
                java.io.File.separator+"system"+java.io.File.separator+
        "test/de/uka/ilkd/key/proof/ruleForTestTacletIndex.taclet");

        ruleRewriteNonH1H2 = NoPosTacletApp.createNoPosTacletApp(taclet("rewrite_noninteractive_h1_h2"));
        ruleNoFindNonH1H2H3 = NoPosTacletApp.createNoPosTacletApp(taclet("nofind_noninteractive_h1_h2_h3"));
        ruleAntecH1 = NoPosTacletApp.createNoPosTacletApp(taclet("rule_antec_h1"));
        ruleSucc = NoPosTacletApp.createNoPosTacletApp(taclet("rule_succ"));
        ruleMisMatch = NoPosTacletApp.createNoPosTacletApp(taclet ("antec_mismatch"));
        notfreeconflict = NoPosTacletApp.createNoPosTacletApp(taclet("not_free_conflict"));
        remove_f = NoPosTacletApp.createNoPosTacletApp(taclet("remove_f"));
        remove_ff = NoPosTacletApp.createNoPosTacletApp(taclet("remove_ff"));
        remove_zero = NoPosTacletApp.createNoPosTacletApp(taclet("remove_zero"));
    }
    
    public void tearDown() {
        ruleRewriteNonH1H2 = null;
        ruleNoFindNonH1H2H3 = null;
        ruleAntecH1 = null;
        ruleSucc = null;
        ruleMisMatch = null;
        notfreeconflict = null;
        remove_f = null;
        remove_ff = null;
        remove_zero = null;       
        realCache = null;
	noCache = null;	
    }

    private final Map<CacheKey, TermTacletAppIndex> termTacletAppIndexCache = new LRUCache<CacheKey, TermTacletAppIndex> ( ServiceCaches.MAX_TERM_TACLET_APP_INDEX_ENTRIES ); 

    private TermTacletAppIndexCacheSet realCache =
        new TermTacletAppIndexCacheSet (termTacletAppIndexCache);

    private TermTacletAppIndexCacheSet noCache =
        new TermTacletAppIndexCacheSet (termTacletAppIndexCache) {
            public ITermTacletAppIndexCache getAntecCache() {
                return getNoCache ();
            }
            public ITermTacletAppIndexCache getSuccCache() {
                return getNoCache ();
            }
    };
    

    public void testIndex0 () {
        doTestIndex0(noCache);
    }

    public void testIndex0WithCache () {
        for ( int i = 0; i != 3; ++i )
            doTestIndex0 ( realCache );
    }

    private void doTestIndex0(TermTacletAppIndexCacheSet cache) {
        Services serv = TacletForTests.services ();

        TacletIndex ruleIdx = new TacletIndex ();
        ruleIdx.add ( remove_f );
        ruleIdx.add ( remove_zero );

        Term term = TacletForTests.parseTerm ( "f(f(f(zero)))=one" );
        SequentFormula cfma = new SequentFormula ( term );

        PosInOccurrence pio = new PosInOccurrence ( cfma, PosInTerm.TOP_LEVEL,
                                                    false );

        TermTacletAppIndex termIdx =
            TermTacletAppIndex.create ( pio, serv, ruleIdx, NullNewRuleListener.INSTANCE,
                                        TacletFilter.TRUE,
                                        cache );

        checkTermIndex ( pio, termIdx );

        // this should not alter the index, as the formula actually
        // did not change
        termIdx = termIdx.update ( pio.down ( 0 ), serv, ruleIdx,
                                   NullNewRuleListener.INSTANCE, cache );

        checkTermIndex ( pio, termIdx );

        // now a real change
        Term term2 = TacletForTests.parseTerm ( "f(f(zero))=one" );
        SequentFormula cfma2 = new SequentFormula ( term2 );
        PosInOccurrence pio2 = new PosInOccurrence ( cfma2,
                                                     PosInTerm.TOP_LEVEL, false );

        termIdx = termIdx.update ( pio2.down ( 0 ).down ( 0 ).down ( 0 ), serv,
                                   ruleIdx, NullNewRuleListener.INSTANCE,
                                   cache );
        checkTermIndex2 ( pio2, termIdx );

        // add a new taclet to the index
        ruleIdx.add ( remove_ff );
        SetRuleFilter filter = new SetRuleFilter ();
        filter.addRuleToSet ( ruleIdx.lookup ( remove_ff.taclet().name () ).rule () );
        termIdx = termIdx.addTaclets ( filter, pio2, serv, ruleIdx,
                                       NullNewRuleListener.INSTANCE );
        checkTermIndex3 ( pio2, termIdx );
    }

    private void checkAtPos(PosInOccurrence pio,
			    TermTacletAppIndex termIdx,
			    ImmutableList<Taclet> list) {
        checkTacletList(termIdx.getTacletAppAt(pio,
                                               TacletFilter.TRUE),
                        list);
    }

    private PosInOccurrence down ( PosInOccurrence pio, int i ) {
	return pio.down(i);
    }

    private void checkTermIndex(PosInOccurrence pio,
                                TermTacletAppIndex termIdx) {
        ImmutableList<Taclet> listA = ImmutableSLList.<Taclet>nil();
        ImmutableList<Taclet> listB = listA.prepend(remove_f.taclet());
        ImmutableList<Taclet> listC = listA.prepend(remove_zero.taclet());
        
        checkAtPos(pio, termIdx, listA);
        checkAtPos(down(pio, 0), termIdx, listB);
        checkAtPos(down(down(pio, 0), 0), termIdx, listB);
        checkAtPos(down(down(down(pio, 0), 0), 0), termIdx, listB);
        checkAtPos(down(down(down(down(pio, 0), 0), 0), 0), termIdx, listC);
        checkAtPos(down(pio, 1), termIdx, listA);
    }

    private void checkTermIndex2(PosInOccurrence pio,
				 TermTacletAppIndex termIdx) {
	ImmutableList<Taclet> listA = ImmutableSLList.<Taclet>nil();
	ImmutableList<Taclet> listB = listA.prepend(remove_f.taclet());
	ImmutableList<Taclet> listC = listA.prepend(remove_zero.taclet());

	checkAtPos(pio, termIdx, listA);
	checkAtPos(down(pio, 0), termIdx, listB);
	checkAtPos(down(down(pio, 0), 0), termIdx, listB);
	checkAtPos(down(down(down(pio, 0), 0), 0), termIdx, listC);
	checkAtPos(down(pio, 1), termIdx, listA);
    }

    private void checkTermIndex3(PosInOccurrence pio,
				 TermTacletAppIndex termIdx) {
	ImmutableList<Taclet> listA = ImmutableSLList.<Taclet>nil();
	ImmutableList<Taclet> listB = listA.prepend(remove_f.taclet());
	ImmutableList<Taclet> listC = listA.prepend(remove_zero.taclet());
	ImmutableList<Taclet> listD = listB.prepend(remove_ff.taclet());

	checkAtPos(pio, termIdx, listA);
	checkAtPos(down(pio, 0), termIdx, listD);
	checkAtPos(down(down(pio, 0), 0), termIdx, listB);
	checkAtPos(down(down(down(pio, 0), 0), 0), termIdx, listC);
	checkAtPos(down(pio, 1), termIdx, listA);
    }


    private void checkTacletList ( ImmutableList<NoPosTacletApp> p_toCheck,
				   ImmutableList<Taclet>         p_template ) {
	assertTrue ( p_toCheck.size () == p_template.size () );
        for (NoPosTacletApp aP_toCheck : p_toCheck) assertTrue(p_template.contains(aP_toCheck.taclet()));
    }
    
}
