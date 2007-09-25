// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//
//

package de.uka.ilkd.key.counterexample;


/**
 * The root of the Calculus Hierarchy, this class only produces the static
 * clauses which are the same for all problems. The subclasses generate the further clauses.
 * @see SortCalculus
 * @see AxiomCalculus
 * @see ConjCalculus
 * @author Sonja Pieper
 * @version 0.1 
 */
public class Calculus {

    private Clauses statics;
    protected Clauses all;

    public Calculus(){

	statics = new Clauses();
        statics.add(this.domainbound());
        statics.add(this.functionality());
        statics.add(this.sameRewriting());
        statics.add(this.resultRewriting());
        statics.add(this.argRewriting());

	all = new Clauses();
        this.addClauses(statics);
    }
    
    public void addClauses(Clauses c){
	this.all.add(c);
    }

    public Clauses getStaticClauses(){
	return statics;
    }
    
    public Clauses getAllClauses(){
        return all;
    }

    private Clauses domainbound(){
	Clauses cs = new Clauses();
	cs.add(new Clause("","max("+CounterExample.config.domainmax+")"));
        return cs;
    }
    
    private Clauses functionality(){
	Clauses cs = new Clauses();
        cs.add(new Clause("intpr(F,X,Y),intpr(F,X,Y1),{Y\\==Y1}",
			  "same(Y,Y1)", "Functionality"));
	cs.add(new Clause("is(X,Y),is(X,Y1),{Y\\==Y1}","same(Y,Y1)"));
        return cs;
    }
    
    private Clauses sameRewriting(){
	Clauses cs = new Clauses();
        cs.add(new Clause("same(X,Y),is(X,Z)","same(Z,Y)","Rewriting with same"));
	cs.add(new Clause("same(X,Y),is(Y,Z)","same(Z,X)"));
	cs.add(new Clause("different(X,Y),is(X,Z)",
			  "different(Z,Y)","Rewriting with different"));
	cs.add(new Clause("different(X,Y),is(Y,Z)","different(Z,X)"));
        return cs;
    }
    
    private Clauses resultRewriting(){
	Clauses cs = new Clauses();
        cs.add(new Clause("intpr(F,X,Y),is(Y,Y1)","intpr(F,X,Y1)","Result rewriting"));
        return cs;
    }
    
    Clauses argRewriting(){
	Clauses cs = new Clauses();
	
	/* rewriting rules where n is the number of args currently produced*/
	for(int n=0; n<=CounterExample.config.maxargs; n++){
	    
	    if(n>0){
		cs.addComment("Rewriting for functions with " +n+" arguments");
            }
	    
	    for(int current_arg=0;current_arg<n;current_arg++){
		String args = new String();
                String rewargs = new String();
                for(int i=1;i<=n;i++){
		    args = args + "X"+i;
                    rewargs = ( i==current_arg ? "Z" : "X"+i );
                }
                String aconj = "is(X"+current_arg+",Z),intpr(F,tup"+n+"("+args+"),Y)";
		String cnsq  = "intpr(F,tup"+n+"("+rewargs+"),Y)";
		
		Clause rewrite_current_arg = new Clause(aconj,cnsq);
		cs.add(rewrite_current_arg);
            }
	}
	
        return cs;
    }
    
    public String toString(){
        return all.toString();
    }
}
