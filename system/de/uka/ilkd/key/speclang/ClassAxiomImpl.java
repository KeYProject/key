// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.speclang;

import java.util.HashMap;
import java.util.Map;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermBuilder;
import de.uka.ilkd.key.logic.op.ProgramVariable;
import de.uka.ilkd.key.proof.OpReplacer;


public final class ClassAxiomImpl implements ClassAxiom {
    
    private static final TermBuilder TB = TermBuilder.DF;
    
    private final String name;
    private final KeYJavaType kjt;    
    private final Term originalAxiom;
    private final ProgramVariable originalSelfVar;
    
    public ClassAxiomImpl(String name, 
	                  KeYJavaType kjt, 
	                  Term axiom,
	                  ProgramVariable selfVar) {
	this.name = name;
	this.kjt = kjt;
	this.originalAxiom = axiom;
	this.originalSelfVar = selfVar;
    }
    

    @Override
    public String getName() {
	return name;
    }
    

    @Override
    public KeYJavaType getKJT() {
	return kjt;
    }
    
    
    @Override
    public Term getAxiom(ProgramVariable selfVar, Services services) {
	Map map = new HashMap();
	map.put(originalSelfVar, selfVar);
	OpReplacer or = new OpReplacer(map);
	return or.replace(originalAxiom);
    }
    
    
    @Override
    public String toString() {
	return originalAxiom.toString();
    }
}
