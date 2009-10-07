// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2009 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.proof.init;

import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.Map;

import de.uka.ilkd.key.collection.ImmutableArray;
import de.uka.ilkd.key.collection.ImmutableSet;
import de.uka.ilkd.key.logic.BasicLocationDescriptor;
import de.uka.ilkd.key.logic.LocationDescriptor;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.AnonymousUpdate;
import de.uka.ilkd.key.logic.op.Function;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.logic.op.QuantifiableVariable;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.updatesimplifier.Update;
import de.uka.ilkd.key.speclang.ClassInvariant;


/**
 * The "CorrectDependsPO" proof obligation.
 */
public class CorrectDependsPO extends AbstractPO {

    private final ImmutableSet<LocationDescriptor> dependsClause;
    private final ClassInvariant inv;


    //-------------------------------------------------------------------------
    //constructors
    //-------------------------------------------------------------------------

    public CorrectDependsPO(InitConfig initConfig,
	    		    ImmutableSet<LocationDescriptor> dependsClause,
                            ClassInvariant inv) {
        super(initConfig,
              "CorrectDepends of \"" + inv + "\"",
              inv.getKJT());
        this.dependsClause = dependsClause;
        this.inv           = inv;
    }



    //-------------------------------------------------------------------------
    //local helper methods
    //-------------------------------------------------------------------------


    private Update createUpdate(UpdateFactory uf, Map<Operator, Function> atPreFunctions) {
        Update result = uf.skip();

        Iterator<LocationDescriptor> it = dependsClause.iterator();
        while(it.hasNext()) {
            LocationDescriptor loc = it.next();
            assert loc instanceof BasicLocationDescriptor;
            BasicLocationDescriptor bloc = (BasicLocationDescriptor) loc;

            Term guardTerm = bloc.getFormula();
            Term locTerm = bloc.getLocTerm();

            APF.createAtPreFunctionsForTerm(guardTerm,
                                            atPreFunctions,
                                            services);
            APF.createAtPreFunctionsForTerm(locTerm,
                                            atPreFunctions,
                                            services);

            Term[] subTermsAtPre = new Term[locTerm.arity()];
            ImmutableArray<QuantifiableVariable>[] boundVars
                = new ImmutableArray[locTerm.arity()];
            for(int i = 0; i < locTerm.arity(); i++) {
                subTermsAtPre[i] = replaceOps(atPreFunctions, locTerm.sub(i));
                boundVars[i] = locTerm.varsBoundHere(i);
            }
            Term locAtIntermediateTerm = TF.createTerm(locTerm.op(),
                                                       subTermsAtPre,
                                                       boundVars,
                                                       null);

            Term locAtPreTerm = replaceOps(atPreFunctions, locTerm);
            Update elementaryUpdate = uf.elementaryUpdate(locAtIntermediateTerm,
                                                          locAtPreTerm);

            Term guardAtPreTerm = replaceOps(atPreFunctions, guardTerm);
            Update guardedUpdate = uf.guard(guardAtPreTerm, elementaryUpdate);

            Update quantifiedUpdate = guardedUpdate;
            Iterator<QuantifiableVariable> it2 = locTerm.freeVars().iterator();
            while(it2.hasNext()) {
                quantifiedUpdate = uf.quantify(it2.next(), quantifiedUpdate);
            }

            result = uf.sequential(result, quantifiedUpdate);
        }

        return result;
    }


    //-------------------------------------------------------------------------
    //methods of ProofOblInput interface
    //-------------------------------------------------------------------------

    public void readProblem(ModStrategy mod) throws ProofInputException {
        //prepare container for @pre-functions
        Map<Operator, Function> atPreFunctions = new LinkedHashMap<Operator, Function>();

        //translate invariant
        Term invTerm = translateInv(inv);

        //build post term
        UpdateFactory uf = new UpdateFactory(services, new UpdateSimplifier());
        Term updateTerm = uf.apply(createUpdate(uf, atPreFunctions), invTerm);
        AnonymousUpdate au = AnonymousUpdate.getNewAnonymousOperator();
        Term postTerm = TF.createAnonymousUpdateTerm(au, updateTerm);

        //build definitions for @pre-functions
        Update atPreDefinitions
            = APF.createAtPreDefinitions(atPreFunctions, services);

        //put everyhing together
        Term poTerm = TB.imp(invTerm, uf.apply(atPreDefinitions, postTerm));
        poTerms = new Term[]{poTerm};

        //register everything in namespaces
        registerInNamespaces(atPreFunctions);
    }


    //-------------------------------------------------------------------------

    protected Term getTerm() {
        return poTerms[0];
    }
}
