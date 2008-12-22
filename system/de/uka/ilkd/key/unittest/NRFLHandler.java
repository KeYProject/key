// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2008 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License.
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.key.unittest;

import java.util.HashSet;
import java.util.LinkedList;

import de.uka.ilkd.key.java.Services;
import de.uka.ilkd.key.java.Statement;
import de.uka.ilkd.key.logic.PosInOccurrence;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.TermFactory;
import de.uka.ilkd.key.logic.UpdateFactory;
import de.uka.ilkd.key.logic.op.ArrayOfQuantifiableVariable;
import de.uka.ilkd.key.logic.op.Location;
import de.uka.ilkd.key.logic.op.NonRigidFunctionLocation;
import de.uka.ilkd.key.logic.op.Operator;
import de.uka.ilkd.key.rule.UpdateSimplifier;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.AssignmentPairImpl;
import de.uka.ilkd.key.rule.updatesimplifier.ListOfAssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.SLListOfAssignmentPair;
import de.uka.ilkd.key.rule.updatesimplifier.Update;

/**
 * Class implemented to fix bug 0895. It deals with  NonRigidFunctionLocations during TestGeneration
 * 
 * @author mbender
 * 
 */
public class NRFLHandler {

    private final UpdateFactory uf;

    private final TermRepHandler trh;

    private final Term result;

    /**
     * The only possibility to create a new NRFLtoLocVar-object
     * 
     * @param serv
     *            The Services of the current proof
     */
    public NRFLHandler(Services serv, TestCodeExtractor tce, PosInOccurrence pos) {
        trh = new TermRepHandler(serv, tce);
        uf = new UpdateFactory(serv, new UpdateSimplifier());

        final Update identUp = createIdentUp(collectNRFLInPost(pos.subTerm()
                .sub(0)));
        final Update compUp = composeUpdate(getOrigUp(pos.constrainedFormula()
                .formula()), identUp);
        initNRFL(compUp);
        result = uf.apply(compUp, TermFactory.DEFAULT.createDiamondTerm(pos
                .subTerm().javaBlock(), createNewPost(pos.subTerm().sub(0))));
    }

    /**
     * This methods creates a new Postcondition by substituting all
     * NonRigidFunctionLocations by their newly created ReadRepresentation
     * 
     * @param post
     * @return The new Postcondition
     */
    private Term createNewPost(Term post) {
        if (post.op() instanceof NonRigidFunctionLocation) {
            return trh.getReadRep(post.op());
        } else {
            final int arity = post.arity();
            if (arity == 0) {
                return post;
            } else {
                final Term[] subs = new Term[arity];
                final ArrayOfQuantifiableVariable[] bVars = new ArrayOfQuantifiableVariable[arity];
                for (int i = 0; i < arity; i++) {
                    subs[i] = createNewPost(post.sub(i));
                    bVars[i] = post.varsBoundHere(i);
                }
                return TermFactory.DEFAULT.createTerm(post.op(), subs, bVars,
                        post.javaBlock());
            }
        }
    }

    /**
     * This method collects all the NRFL that occur in the Postcondition
     * In the example
     * 
     *  \forall jint i; \exists jint j; getAtPre_0(aAtPre_0, i) = a[j]
     * 
     *  it returns
     *  
     *          {aAtPre_0,getAtPre_0(aAtPre_0, i)}
     * 
     * @param postCond
     *            The Term to be examined
     * @return A HashSet containing all the NRFLs in the Postcondition
     */
    private HashSet<Term> collectNRFLInPost(Term postCond) {
        final HashSet<Term> result = new HashSet<Term>();
        if (postCond.op() instanceof NonRigidFunctionLocation) {
            result.add(postCond);
        }
        if (postCond.arity() > 0) {
            for (int i = 0; i < postCond.arity(); i++) {
                result.addAll(collectNRFLInPost(postCond.sub(i)));
            }
        }
        return result;
    }

    /**
     * This method creates an identity Update. Every Term of the given HashSet
     * is assigned to itself.
     * 
     * {aAtPre_0:=aAtPre_0 ||
     *         getAtPre_0(aAtPre_0,i):=getAtPre_0(aAtPre_0,i)}
     * 
     * @param funcs
     *            The HashSet of NRFL for which the Updates should be created
     * @return The created identity Update. Looks like identUp =
     *         
     */
    private Update createIdentUp(HashSet<Term> funcs) {
        ListOfAssignmentPair newAssPairs = SLListOfAssignmentPair.EMPTY_LIST;
        for (Term NRFL : funcs) {
            newAssPairs = newAssPairs.append(new AssignmentPairImpl(
                    (NonRigidFunctionLocation) NRFL.op(), getSubs(NRFL), NRFL));
        }
        return Update.createUpdate(newAssPairs.toArray());
    }

    /**
     * A helper method, that creates an Array that contains all the Subformulas
     * of the given Term
     * 
     * @param term
     *            the Term for which one wants all subterms
     * @return An Array containing all subterms
     */
    private Term[] getSubs(Term term) {
        final Term[] subs = new Term[term.arity()];
        for (int i = 0; i < subs.length; i++) {
            subs[i] = term.sub(i);
        }
        return subs;
    }

    /**
     * Creates a new update by combining both arguments. This is done similar to
     * KeY's 'applyUpdate()' with the difference, that the Update is only
     * applied on the rhs of the AssignmentPair. All quantified update are
     * removed.
     * 
     * {_a:=a || aAtPre_0:=a ||\for (int x1; jint[] x0)
     * getAtPre_0(x0,x1):=x0[x1]} 
     * {aAtPre_0:=aAtPre_0 ||
     * getAtPre_0(aAtPre_0,i):=getAtPre_0(aAtPre_0,i)}
     * 
     * =>
     * 
     * {_a:=a || aAtPre_0:=a || getAtPre_0(a,i):= a[i] }
     * 
     * @param origUp
     *            The original update of the Term
     * @param IdentUp
     *            The created Ident-Update
     * @return The new Update
     */
    private Update composeUpdate(Update origUp, Update IdentUp) {
        int origSize = origUp.locationCount();
        int identSize = IdentUp.locationCount();
        LinkedList<AssignmentPair> newAssPairs = new LinkedList<AssignmentPair>();
        for (int i = 0; i < origSize; i++) {
            if (origUp.getAssignmentPair(i).boundVars().size() == 0) {
                newAssPairs.add(origUp.getAssignmentPair(i));
            }
        }
        AssignmentPair newAss;
        for (int i = 0; i < identSize; i++) {
            newAss = createAss(origUp, IdentUp.getAssignmentPair(i));
            if (!newAssPairs.contains(newAss)) {
                newAssPairs.add(newAss);
            }
        }
        return Update.createUpdate(newAssPairs
                .toArray(new AssignmentPair[newAssPairs.size()]));
    }

    /**
     * This method iterates through the given Update and creates a
     * TermRepresentation for every NRFL
     * 
     * @param up
     */
    private void initNRFL(Update up) {
        Term currTerm;
        AssignmentPair newAss;
        for (int i = 0; i < up.locationCount(); i++) {
            newAss = up.getAssignmentPair(i);
            currTerm = newAss.locationAsTerm();
            if (currTerm.op() instanceof NonRigidFunctionLocation) {
                trh.add(newAss);
            }
        }
    }

    /**
     * This method is the core part of composeUpdate(). It creates a new
     * AssignmentPair be taking the rhs of the identity AssPair and applying the
     * original Update on it. The computed result is the rhs of the new AssPair.
     * The lhs is just taken from the identity-AssPair
     * 
     * @param origUp the original Update of the Formula
     * @param curr the current AssPair of the Identity Update
     * @return the new AssPair
     */
    private AssignmentPair createAss(Update origUp, AssignmentPair curr) {
        final Term currTerm = curr.locationAsTerm();
        return new AssignmentPairImpl((Location) currTerm.op(),
                getSubs(currTerm), uf.apply(origUp, curr.value()));
    }

    private Update getOrigUp(Term t) {
        return Update.createUpdate(t);
    }

    public Statement getWriteRep(Operator op) {
        return trh.getWriteRep(op);
    }

    public Term getResult() {
        return result;
    }

}
