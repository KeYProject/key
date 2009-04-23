// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//This file is part of KeY - Integrated Deductive Software Design
//Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                      Universitaet Koblenz-Landau, Germany
//                      Chalmers University of Technology, Sweden
//
//The KeY system is protected by the GNU General Public License. 
//See LICENSE.TXT for details.
//
//
package de.uka.ilkd.key.strategy.quantifierHeuristics;

import junit.framework.TestCase;
import de.uka.ilkd.key.gui.configuration.ProofSettings;
import de.uka.ilkd.key.java.VarAndType;
import de.uka.ilkd.key.java.abstraction.KeYJavaType;
import de.uka.ilkd.key.java.declaration.ClassDeclaration;
import de.uka.ilkd.key.logic.*;
import de.uka.ilkd.key.logic.op.*;
import de.uka.ilkd.key.logic.sort.*;
import de.uka.ilkd.key.proof.*;
import de.uka.ilkd.key.rule.TacletForTests;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPairImpl;
import de.uka.ilkd.key.rule.updatesimplifier.Update;


//most Code are copyed from Logic.TestUpdateFactory

public class TestTriggersSet extends TestCase {

	private Proof proof;

	private TermFactory tf = TermFactory.DEFAULT;
	private TermBuilder tb = TermBuilder.DF;
    
	private Namespace variables = new Namespace();

	private Namespace functions = new Namespace();

	private Namespace sorts = new Namespace();

	//sort 
	private Sort r;
	private Sort s;
	private Sort t;
	//private Sort ints ;
	
	
	//constant function
	private Function r_a;
	private Function r_b;
	private Function r_c;

	private Function s_a;
	private Function s_b;
	private Function s_c;

	private Function t_a;
	private Function t_b;
	private Function t_c;
	
	//Rigid function
	private Function frr; // r->r
	private Function f2rr; // r->r
	private Function fsr; // s-> r
	private Function ftr; // t->r
	private Function fstr;// s->t->r
	private Function frstr;//r->s->t->r;
	
	private Function gss; // s->s
	private Function grs; // r->s
	private Function gts; // t->s
	private Function grts; //r->t->s
	private Function grsts;//r->s->t->s
   
	private Function htt; // t->t
	private Function hrt; // r -> t
	private Function hst; // s->t
	private Function hrst;// r->s->t
	private Function hrstt;//t->s->t->t
    
	//Formular function
	private Function pp;//Formula->Formula
	private Function pr;//r->Formula
	private Function ps;//s->Formula
	private Function pt;//t->Formula
	private Function prs;//r->s->Formula
	private Function pst;//s->t->Formula
	private Function prt;//r->t->Formula
        private Function prst;//r->s->t->Formula
       // private Function pi;//ints->Formula
        private Goal g;
	
	public TestTriggersSet() {
		super();
	}

	public void setUp() {
		//sort
		r = new PrimitiveSort(new Name("r"));
		s = new PrimitiveSort(new Name("s"));
		t = new PrimitiveSort(new Name("t"));
		//ints = ProofSettings.DEFAULT_SETTINGS.getLDTSettings().getIntegerSemantics().getIntSort();
		sorts.add(r);
		sorts.add(s);
		sorts.add(t);
		//sorts.add(ints);
		
		//constant
		r_a = new RigidFunction(new Name("r_a"), r, new Sort [0]);
		r_b = new RigidFunction(new Name("r_b"), r, new Sort [0]);
		r_c= new RigidFunction(new Name("r_c"), r, new Sort [0]);
		functions.add(r_a);
		functions.add(r_b);
		functions.add(r_c);
		
		s_a = new RigidFunction(new Name("s_a"), s, new Sort [0]);
		s_b = new RigidFunction(new Name("s_b"), s, new Sort [0]);
		s_c= new RigidFunction(new Name("s_c"), s, new Sort [0]);
		functions.add(s_a);
		functions.add(s_b);
		functions.add(s_c);
        
		t_a = new RigidFunction(new Name("t_a"), s, new Sort [0]);
		t_b = new RigidFunction(new Name("t_b"), s, new Sort [0]);
		t_c = new RigidFunction(new Name("t_c"), s, new Sort [0]);
		functions.add(t_a);
		functions.add(t_b);
		functions.add(t_c);
        
        
        	        //function
		frr = new RigidFunction(new Name("frr"), r, new Sort[] { r });
		f2rr = new RigidFunction(new Name("f2rr"), r, new Sort[] { r });
		fsr = new RigidFunction(new Name("fsr"), r, new Sort[] { s });
		ftr = new RigidFunction(new Name("ftr"), r, new Sort[] { t });
		fstr= new RigidFunction(new Name("fst"),r, new Sort[] {s,t});
		frstr=new RigidFunction(new Name("frstr"),r,new Sort[]{r,s,t});
		
		functions.add(frr);
		functions.add(f2rr);
		functions.add(fsr);
		functions.add(ftr);
		functions.add(fstr);
		functions.add(frstr);
        
		gss = new RigidFunction(new Name("gss"), s, new Sort[] { s });
		grs = new RigidFunction(new Name("grs"), s, new Sort[] { r });
		gts = new RigidFunction(new Name("gts"), s, new Sort[] { t });
		grts= new RigidFunction(new Name("grts"),s, new Sort[] {r,t});
		grsts=new RigidFunction(new Name("grsts"),s,new Sort[]{r,s,t});

		functions.add(gss);
		functions.add(grs);
		functions.add(gts);
		functions.add(grts);
		functions.add(grsts);
        
		htt = new RigidFunction(new Name("htt"), t, new Sort[] { t });
		hrt = new RigidFunction(new Name("hrt"), t, new Sort[] { r });
		hst = new RigidFunction(new Name("hst"), t, new Sort[] { s });
		hrst= new RigidFunction(new Name("hrst"),t, new Sort[] {r,s});
		hrstt=new RigidFunction(new Name("hrstt"),t,new Sort[]{r,s,t});
	
		functions.add(htt);
		functions.add(hrt);
		functions.add(hst);
		functions.add(hrst);
		functions.add(hrstt);
        
		//Formula function
		pp=new RigidFunction(new Name("pp"),Sort.FORMULA,
				                    new Sort[]{Sort.FORMULA});
		pr=new RigidFunction(new Name("pr"),Sort.FORMULA,new Sort[]{r});
		ps=new RigidFunction(new Name("ps"),Sort.FORMULA,new Sort[]{s});
		pt=new RigidFunction(new Name("pt"),Sort.FORMULA,new Sort[]{t});
		prs=new RigidFunction(new Name("prs"),Sort.FORMULA,
				        new Sort[]{r,s});
		prt=new RigidFunction(new Name("prt"),Sort.FORMULA,
				        new Sort[]{r,t});
		pst=new RigidFunction(new Name("pst"),Sort.FORMULA,
				        new Sort[]{s,t});
		prst=new RigidFunction(new Name("prst"),Sort.FORMULA,
				        new Sort[]{r,s,t});
		//pi=new RigidFunction(new Name("pi"),Sort.FORMULA,new Sort[]{});
		functions.add(pp);
		functions.add(pr);
		functions.add(ps);
		functions.add(pt);
		functions.add(prs);
		functions.add(prt);
		functions.add(pst);
		functions.add(prst);
		//functions.add(pi);
		
		proof = new Proof(TacletForTests.services());
		g = new Goal(new Node(proof, Sequent.EMPTY_SEQUENT),
				new RuleAppIndex(new TacletAppIndex(new TacletIndex()),
						new BuiltInRuleAppIndex(new BuiltInRuleIndex())));
		proof.setRoot(g.node());
		proof.add(g);

		proof.setNamespaces(new NamespaceSet(variables, functions, sorts,
				new Namespace(), new Namespace(),new Namespace() ));

	}

	private Term parseTerm(String termstr) {
		return TacletForTests.parseTerm(termstr, new NamespaceSet(
				variables, functions, sorts, new Namespace(),
				new Namespace(), new Namespace()));
	}

	public void testTrigger1(){
		String term1 = "\\forall s x;(ps(x))";
		Term allterm = parseTerm(term1);
		Term trigger1= allterm.sub(0);
		TriggersSet ts = TriggersSet.create(allterm, proof.getServices());
		int triggerNum = ts.getAllTriggers().size();
		assertEquals (1,triggerNum);
		Term trigger2 = ts.getAllTriggers().iterator().next().getTriggerTerm();
		assertEquals (trigger1,trigger2);
	}
	 
	public void testTrigger2(){
		String term1 = "\\forall r x;(frr(x)=frr(frr(x)))";
		Term allterm = parseTerm(term1);
		Term trigger1= allterm.sub(0).sub(1);
		TriggersSet ts = TriggersSet.create(allterm, proof.getServices());
		int triggerNum = ts.getAllTriggers().size();
		assertEquals (1,triggerNum);
		Term trigger2 = ts.getAllTriggers().iterator().next().getTriggerTerm();
		assertEquals (trigger1,trigger2);
	}
}
