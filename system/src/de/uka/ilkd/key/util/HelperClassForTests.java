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

/*
 * Created on 18.12.2004
 */
package de.uka.ilkd.key.util;

import java.io.File;

import de.uka.ilkd.key.collection.ImmutableSLList;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.JavaProfile;
import de.uka.ilkd.key.proof.init.KeYUserProblemFile;
import de.uka.ilkd.key.proof.init.ProblemInitializer;
import de.uka.ilkd.key.proof.init.Profile;
import de.uka.ilkd.key.proof.init.ProofInputException;
import de.uka.ilkd.key.proof.init.RuleCollection;
import de.uka.ilkd.key.proof.io.RuleSource;
import de.uka.ilkd.key.rule.BuiltInRule;

/**
 * @author bubel
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class HelperClassForTests {
    
    private static final Profile profile = new JavaProfile() {
            //we do not want normal standard rules, but ruleSetsDeclarations is needed for string library (HACK)
	    public RuleCollection getStandardRules() {
                return new RuleCollection(
                                RuleSource.initRuleFile("LDTsForTestsOnly.key"), 
                                ImmutableSLList.<BuiltInRule>nil());
            }
        };
    
    public HelperClassForTests() {
        
    }
    
    public ProofAggregate parse(File file) {
        return parse(file, profile);
    }
    
    public ProofAggregate parse(File file, Profile profile) {
        ProblemInitializer pi = null;
        ProofAggregate result = null;
       
        try {	    
            KeYUserProblemFile po 
            	= new KeYUserProblemFile("UpdatetermTest", file, null, profile); 
            pi = new ProblemInitializer(profile);
           
            pi.startProver(po, po);
            result = po.getPO();                            

        } catch (Exception e) {
            System.err.println("Exception occurred while parsing "+file+"\n");
            e.printStackTrace();
            System.exit(-1);
        }
        return result;
    }
    
    public ProofAggregate parseThrowException(File file) throws ProofInputException{        
        return parseThrowException(file, profile);
    }
       
    
    public ProofAggregate parseThrowException(File file, Profile profile) throws ProofInputException{
	KeYUserProblemFile po 
		= new KeYUserProblemFile("UpdatetermTest", file, null, profile); 
        ProblemInitializer pi = new ProblemInitializer(profile);
        pi.startProver(po, po);
        return po.getPO();        
    }
       
    public Term extractProblemTerm(Proof p) {
        return p.root().sequent().succedent().iterator().next().formula();
    }

}
