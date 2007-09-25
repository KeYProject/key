// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.tree;


import java.util.Iterator;

import de.uka.ilkd.asmkey.parser.ast.*;
import de.uka.ilkd.asmkey.parser.env.*;
import de.uka.ilkd.asmkey.rule.*;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.logic.Sequent;
import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.logic.op.SetAsListOfSchemaVariable;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;
import de.uka.ilkd.key.rule.*;




/** Class to parse taclets declarations.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen
 */
final class TacletDeclarationParser {

    private static TacletBuilder createTacletBuilder(Term term) {
        return new RewriteTacletBuilder().setFind(term);
    }

    private static TacletBuilder createTacletBuilder(Sequent sequent, Location location)
        throws ParserException
    {
        if (sequent.isEmpty()) {
            return new NoFindTacletBuilder();
        } else if (sequent.antecedent().size() == 1
                   && sequent.succedent().size() == 0) {
            return new AntecTacletBuilder().setFind(sequent.antecedent().get(0).formula());
        } else if (sequent.antecedent().size() == 0
                   && sequent.succedent().size() == 1) {
            return new SuccTacletBuilder().setFind(sequent.succedent().get(0).formula());
        } else {
            throw new ParserException("Invalid find-sequent in " + sequent + ".", location);
        }
    }

    /* Hint: protected access because method is called from inner
     * class. */
    protected static void addGoalReplace(TacletBuilder tb,
                                         String id,
                                         Term term,
                                         Sequent sequent,
                                         Sequent addSequent,
                                         ListOfTaclet addRules,
                                         Location location)
        throws ParserException
    {
        TacletGoalTemplate gt = null;
        if (term == null && sequent == null) {
            gt = new TacletGoalTemplate(addSequent,
                                        addRules,
                                        SetAsListOfSchemaVariable.EMPTY_SET);
        } else if (tb instanceof NoFindTacletBuilder) {
            // there is a replacewith without a find.
            throw new ParserException("Replacewith without find.", location);
        } else if (tb instanceof SuccTacletBuilder || tb instanceof AntecTacletBuilder) {
            if (sequent != null) {
                gt = new AntecSuccTacletGoalTemplate(addSequent,
                                                     addRules,
                                                     sequent,
                                                     SetAsListOfSchemaVariable.EMPTY_SET);
            } else {
                throw new ParserException("Replacewith does not match find. " + term, location);
            }
        } else if (tb instanceof RewriteTacletBuilder) {
            if (term != null) {
                gt = new RewriteTacletGoalTemplate(addSequent,
                                                   addRules,
                                                   term,
                                                   SetAsListOfSchemaVariable.EMPTY_SET);
            } else {
                throw new ParserException("Replacewith does not match find. " + sequent, location);
            }
        }
        gt.setName(id);
        tb.addTacletGoalTemplate(gt);
    }

    /* Hint: protected access because method is called from inner
     * class. */
    protected static Term parseNullTerm(TermEnvironment env, AstTerm term)
        throws ParserException
    {
        if (term == null) {
            return null;
        } else {
            return TermParser.parseTerm(env, term);
        }
    }

    /* Hint: protected access because method is called from inner
     * class. */
    protected static Sequent parseNullSequent(TermEnvironment env, AstSequent sequent)
        throws ParserException
    {
        if (sequent == null) {
            return null;
        } else {
            return TermParser.parseSequent(env, sequent);
        }
    }

    /* Hint: protected access because method is called from inner
     * class. */
    protected static Sequent parseEmptySequent(TermEnvironment env, AstSequent sequent)
        throws ParserException
    {
        if (sequent == null) {
            return Sequent.EMPTY_SEQUENT;
        } else {
            return TermParser.parseSequent(env, sequent);
        }
    }

    /* Hint: protected access because method is called from inner
     * class. */
    /** Parses recursively a list of taclets and return these
     * taclets. The taclets are not added to the given environment. */
    protected static ListOfTaclet getListOfTaclet(DeclarationEnvironment env,
						  AstTacletDeclaration[] addRules)
        throws ParserException
    {
        ListOfTaclet list = SLListOfTaclet.EMPTY_LIST;
        if (addRules != null) {
            TacletEnvironment tacletEnv = new TacletEnvironment(env);
	    // TO REVISE
            //TreeParser.parseDeclarations(tacletEnv, addRules, ModStrategy.MOD_ALL);
            for (Iterator i = tacletEnv.getLocalTaclets().iterator(); i.hasNext();) {
                Taclet taclet = (Taclet) i.next();
                list = list.append(taclet);
            }
        }
        return list;
    }

    /** Parse a taclet in the given environment and add it to this
     * environment. Identifier is the name of the taclet. */
    public static void parse(final DeclarationEnvironment env,
			     final Identifier id,
			     final Name name, AstTaclet taclet)
    throws ParserException {
        /* Hint: This method is quite long, because it uses a lot of
         * inner classes for the different visitors. The code itself
         * is very simple. */
        try {
            /* create a suitable TacletBuilder */
            final TacletBuilder tb =
                taclet.getTerm() != null
                ? createTacletBuilder(TermParser.parseTerm(env, taclet.getTerm()))
                : createTacletBuilder(TermParser.parseSequent(env, taclet.getSequent()),
                                      taclet.getSequent().getLocation());
            tb.setName(name);
            /* if sequent */
            if (taclet.getIfSeq() != null) {
                tb.setIfSequent(TermParser.parseSequent(env, taclet.getIfSeq()));
            }
            /* list of conditions */
            for (Iterator i = taclet.getConditions().iterator(); i.hasNext();) {
                AstCondition cond = (AstCondition) i.next();
                cond.accept(new AstConditionVisitor() {

                        public void visitOperatorEquals(boolean equal, Identifier v, Identifier w)
			throws ParserException {
			    tb.addVariableCondition
				(new OperatorEqualsCondition
				 (equal,
				  EnvironmentUtil.getSchemaVariable(env, v),
				  EnvironmentUtil.getSchemaVariable(env, w)));
                        }

                        public void visitNotFreeIn(Identifier v, Identifier w)
			throws ParserException {
			    tb.addVarsNotFreeIn
				(EnvironmentUtil.getSchemaVariable(env, v),
				 EnvironmentUtil.getSchemaVariable(env, w));
                        }

                        public void visitPure(Identifier v)
			throws ParserException {
			    tb.addVariableCondition
				(new PureCondition(EnvironmentUtil.getSchemaVariable(env, v)));
                        }

                        public void visitStatic(Identifier v) 
			throws ParserException {
			    tb.addVariableCondition
				(new StaticCondition(EnvironmentUtil.getSchemaVariable(env, v)));
                        }

                        public void visitStaticArgs(Identifier v) 
			throws ParserException {
			    tb.addVariableCondition
				(new StaticArgsCondition
				 (EnvironmentUtil.getSchemaVariable(env, v)));
                        }

                        public void visitDynamic(Identifier v)
			throws ParserException {
			    tb.addVariableCondition
				(new DynamicCondition(EnvironmentUtil.getSchemaVariable(env, v)));
                        }

			public void visitAtomic(Identifier v)
			throws ParserException {
			    tb.addVariableCondition
				(new AtomicCondition(EnvironmentUtil.getSchemaVariable(env, v)));
			}

                        public void visitDerived(Identifier v)
			throws ParserException {
			    tb.addVariableCondition
				(new DerivedCondition(EnvironmentUtil.getSchemaVariable(env, v)));
                        }

                        public void visitSkolem(Identifier v, Identifier w)
			throws ParserException {
			    tb.addVarsNewDependingOn
				(EnvironmentUtil.getSchemaVariable(env, v),
				 EnvironmentUtil.getSchemaVariable(env, w));
                        }

			public void visitMayUpdate(boolean may, Identifier r, Identifier f)
			throws ParserException {
			    tb.addVariableCondition
				(new MayUpdateCondition
				 (may,
				  EnvironmentUtil.getSchemaVariable(env, r),
				  EnvironmentUtil.getSchemaVariable(env, f)));
			}

			public void visitMayAccess(boolean may, Identifier r, Identifier f)
			throws ParserException {
			    tb.addVariableCondition
				(new MayAccessCondition
				 (may,
				  EnvironmentUtil.getSchemaVariable(env, r),
				  EnvironmentUtil.getSchemaVariable(env, f)));
			}

                    });
            }

            /* goals */
            for (Iterator i = taclet.getGoals().iterator(); i.hasNext();) {
                AstGoal goal = (AstGoal) i.next();
                final Location location = goal.getLocation();
                goal.accept(new AstGoalVisitor() {

                        public void visitReplace(String name, AstTerm term, AstSequent addSequent,
                                                 AstTacletDeclaration[] addRules)
			throws ParserException {
			    addGoalReplace(tb,
					   name,
					   parseNullTerm(env, term),
					   null,
					   parseEmptySequent(env, addSequent),
					   getListOfTaclet(env, addRules),
					   location);
                        }

                        public void visitReplace(String name,
                                                 AstSequent sequent,
                                                 AstSequent addSequent,
                                                 AstTacletDeclaration[] addRules)
			throws ParserException {
			    addGoalReplace(tb,
					   name,
					   null,
					   parseNullSequent(env, sequent),
					   parseEmptySequent(env, addSequent),
					   getListOfTaclet(env, addRules),
					   location);
                        }

			public void visitReplace(String name,
						 AstSequent sequent) {
			    /*addGoalReplace(tb,
                                               name,
					       
                                               location);*/
			}

                    });
            }

            /* modifiers */
            for (Iterator i = taclet.getModifiers().iterator(); i.hasNext();) {
                AstTacletModifier mod = (AstTacletModifier) i.next();
                mod.accept(new AstTacletModifierVisitor() {

                        public void visitHeuristics(Identifier[] ids)
			throws ParserException {
			    for (int j = 0; j < ids.length; ++j) {
				tb.addRuleSet(EnvironmentUtil.getRuleSet(env, ids[j]));
			    }
                        }

                        public void visitNonInteractive() {
                            tb.setNoninteractive(true);
                        }                   

                        public void visitDisplayName(String displayName) {
                            tb.setDisplayName(displayName);
                        }

                        public void visitHelpText(String helpText) {
                            tb.setHelpText(helpText);
                        }

			public void visitSameUpdateLevel()
			    throws ParserException {
			    if (tb instanceof RewriteTacletBuilder) {
				((RewriteTacletBuilder)tb).setStateRestriction(RewriteTaclet.SAME_UPDATE_LEVEL);
			    } else {
				throw new ParserException
				    ("\"\\sameUpdateLevel\" may only be used for rewrite taclets:",
				     id.getLocation());
			    }
			}

			public void visitInSequentState()
			    throws ParserException {
			    if (tb instanceof RewriteTacletBuilder) {
				((RewriteTacletBuilder)tb).setStateRestriction(RewriteTaclet.IN_SEQUENT_STATE);
			    } else {
				throw new ParserException
				    ("\"\\inSequentState\" may only be used for rewrite taclets:",
				     id.getLocation());
			    }
			}

                    });
            }
            env.addTaclet(tb.getTaclet());
        } catch (EnvironmentException ee) {
            throw new ParserException(ee.getMessage(),
				      id.getLocation());
        }

    }

}
