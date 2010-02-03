// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
/*
 * Created on 18.12.2004
 */
package de.uka.ilkd.key.util;

import java.io.File;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.proof.ProofAggregate;
import de.uka.ilkd.key.proof.init.*;

/**
 * @author bubel
 *
 * TODO To change the template for this generated type comment go to
 * Window - Preferences - Java - Code Style - Code Templates
 */
public class HelperClassForTests {
    
    private static Profile JUNIT_PROFILE = new JUnitTestProfile();
    
    public HelperClassForTests() {
        
    }
    
    public ProofAggregate parse(File file) {
        return parse(file, JUNIT_PROFILE);
    }
    
    public ProofAggregate parse(File file, Profile profile) {
        ProblemInitializer pi = null;
        ProofAggregate result = null;
       
        try {	    
            KeYUserProblemFile po 
            	= new KeYUserProblemFile("UpdatetermTest", file, null); 
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
        return parseThrowException(file, JUNIT_PROFILE);
    }
       
    
    public ProofAggregate parseThrowException(File file, Profile profile) throws ProofInputException{
	KeYUserProblemFile po 
		= new KeYUserProblemFile("UpdatetermTest", file, null); 
        ProblemInitializer pi = new ProblemInitializer(profile);
        pi.startProver(po, po);
        return po.getPO();        
    }
       
    public Term extractProblemTerm(Proof p) {
        return p.root().sequent().succedent().iterator().next().formula();
    }

}
