// This file is part of KeY - Integrated Deductive Software Design
// Copyright (C) 2001-2005 Universitaet Karlsruhe, Germany
//                         Universitaet Koblenz-Landau, Germany
//                         Chalmers University of Technology, Sweden
//
// The KeY system is protected by the GNU General Public License. 
// See LICENSE.TXT for details.
//
//

package de.uka.ilkd.asmkey.parser.ast;

import de.uka.ilkd.asmkey.parser.tree.ParsingStack;
import de.uka.ilkd.asmkey.unit.ExportInfo;
import de.uka.ilkd.asmkey.unit.ImportInfo;
import de.uka.ilkd.asmkey.util.ArrayUtil;
import de.uka.ilkd.key.logic.Name;
import de.uka.ilkd.key.parser.Location;
import de.uka.ilkd.key.parser.ParserException;

/** Implementation for abstract factory {@link AstFactory}. The
 * factory uses inner, anonymous classes to implement the various AST
 * nodes. They may only be accessed with the visitors.
 *
 * @author Hubert Schmid
 * @author Stanislas Nanchen 
 */

public final class AstFactoryImpl implements AstFactory {

    /* --- type reference --- */
   
    public AstType createPrimitiveTypeRef(Location location, Identifier sort) {
	return new AstType(location, sort, false);
    }
    
    public AstType createSequenceTypeRef(Location location, Identifier sort) {
	return new AstType(location, sort, true);
    }
    
    public AstType createAsmRuleTypeRef(Location location) {
	return AstType.createAsmRuleTypeRef(location);
    }

    public AstSchemaType createSchemaTypeRef(final Location location,
					  final PrimitiveSchemaType type, final boolean rigid) {
        return new AstSchemaType(location) {

                public void accept(AstSchemaTypeVisitor visitor)
		throws ParserException {
                    visitor.visitPrimitive(type, rigid, location);
                }

                public String toString() {
                    return "[SchemaType:type=" + type + ",rigid=" + rigid + "]";
                }

            };
    }

    public AstSchemaType createComposedSchemaTypeRef(final Location location,
                                          final AstType sort, final boolean rigid) {
        return new AstSchemaType(location) {

                public void accept(AstSchemaTypeVisitor visitor) 
		throws ParserException {
                    visitor.visitComposed(sort, rigid, location);
                }

                public String toString() {
                    return "[SchemaType:sort=" + sort + ",rigid=" + rigid + "]";
                }

            };
    }

    public AstSchemaType createDependingSchemaTypeRef(final Location location, final AstType sort) {
        return new AstSchemaType(location) {

                public void accept(AstSchemaTypeVisitor visitor) 
		throws ParserException {
                    visitor.visitDepending(sort, location);
                }

                public String toString() {
                    return "[SchemaType:sort=" + sort + ",constant]";
                }

            };
    }

    public AstSchemaType createVariableSchemaTypeRef(final Location location, final AstType sort) {
	return new AstSchemaType(location) {

                public void accept(AstSchemaTypeVisitor visitor) 
		throws ParserException {
                    visitor.visitVariable(sort, location);
                }

                public String toString() {
                    return "[SchemaType:sort=" + sort + ",variable]";
                }

            };
    }

    /* --- first order logic terms --- */

    public AstTerm createTerm(final Location location,
			      final AstOperator op,
			      final AstTerm[] terms) {
        return new AstTerm(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		    throws ParserException
		{
		    return visitor.visitOperatorTerm
			(closure, op, (AstTerm[]) ArrayUtil.copy(terms), location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstTerm:op=" + op + ",terms=" + ArrayUtil.toString(terms) + "]";
                }

            };
    }

    public AstTerm createBigTerm(final Location location,
				 final AstOperator op,
				 final Identifier sort,
				 final Identifier func,
				 final Identifier narity,
				 final AstTerm form) {
	return new AstTerm(location) {

		public Object accept(AstTermVisitor visitor, ParsingStack closure)
		    throws ParserException
		{
		    return visitor.visitBigTerm(closure, op, sort, func, narity, form);
		}

		/** for debug only */
		public String toString() {
		    return "[AstTerm:op=" + op +",func=" + func + ",formula=" + form;
		}

	    };
    }

    public AstTerm createTerm(final Location location,
                              final AstQuantifier q,
                              final Identifier var,
                              final Identifier sort,
                              final AstTerm term) {
        return new AstTerm(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
		    return visitor.visitQuantifierTerm(closure, q, var, sort, term, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstTerm:q=" + q + ",var=" + var + ",term=" + term + "]";
                }

            };
    }

    public AstTerm createTerm(final Location location,
			      final Identifier id,
			      final AstTerm[] terms) {
        return new AstTerm(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
		    return visitor.visitFunctionTerm
			(closure, id, (AstTerm[]) ArrayUtil.copy(terms), location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstTerm:id=" + id + ",terms=" + ArrayUtil.toString(terms) + "]";
                }

            };
    }

    public AstTerm createSubstitutionTerm(final Location location,
                                          final Identifier var,
                                          final Identifier sort,
                                          final AstTerm subst,
                                          final AstTerm term,
					  final boolean waryEx,
					  final boolean waryAll) {
        return new AstTerm(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
		    return visitor.visitSubstitutionTerm
			(closure, var, sort, subst, term, waryEx, waryAll, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstTerm:var=" + var + ",sort=" + sort + ",subst=" +
			subst + ",term=" + term + "]";
                }

            };
    }


    public AstTerm createFunctionTerm(final Location location,
				      final Identifier id,
				      final AstTerm func,
				      final AstTerm form) {
	return new AstTerm(location) {
		
		public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
		    return visitor.visitFunctionTerm(closure, id, func, form, location);
		}

		/** for debug only */
		public String toString() {
		    return "[AstTerm:id=" + id + "func=" + func + ",form=" + form + "]";
		}
	    };
    }

    public AstTerm createAbbreviationTerm(final Location location, final Identifier name) {
        return new AstTerm(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
		    return visitor.visitAbbreviationTerm(closure, name, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstTerm:abbr=" + name + "]";
                }

            };
    }

    /* --- sequences and sets */

    // public AstTerm createSetTerm(Location location, final AstTerm[] elems)
    //{
	    //return new AstTerm(location) {
		
	    //	public Object accept(AstTermVisitor visitor, ParsingStack closure) {
	    //	    return visitor.visitSetTerm(closure, elems);
	    //	}
    //
		/** for debug only */
    //		public String toString() {
    //		    String elemsString = elems==null?"":elems.toString();
    //		    return "[AstTerm:set=:[" + elemsString + "]";
    //		}
    //	    };
    //    }



    public AstTerm createSequenceTerm(final Location location,
				      final Identifier basesort,
				      final AstTerm[] elems, final AstTerm tail)
    {
    	return new AstTerm(location) {
    		
    		public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
		    return visitor.visitSequenceTerm(closure, basesort, elems, tail, location);
    		}
		
   		/** for debug only */
   		public String toString() {
   		    String elemsString = elems==null?"":elems.toString();
   		    String tailString = tail==null?"":tail.toString();
    		    return "[AstTerm:sequence=:<" + elemsString + ":" + tailString + ">";
    		}
    	    };
        }

    /* --- dynamic logic --- */

    public AstTerm createDlBox(final Location location,
			       final AstAsmRule rule,
			       final AstTerm term,
			       final AstTerm step) {
        return new AstTerm(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		    throws ParserException {
		    return visitor.visitBox(closure, rule, term, step, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstTerm(Box):rule=" + rule + ",term=" + term + "]";
                }

            };
    }

    public AstTerm createDlDiamond(final Location location,
				   final AstAsmRule rule,
				   final AstTerm term,
				   final AstTerm step) {
        return new AstTerm(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure) 
		    throws ParserException {
		    return visitor.visitDiamond(closure, rule, term, step, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstTerm(Diamond):rule=" + rule + ",term=" + term + "]";
                }

            };
    }

		
    /* --- taclets --- */

    public AstCondition createOperatorEqualsCondition(Location location,
                                                      final boolean equal,
                                                      final Identifier v,
                                                      final Identifier w) {
        return new AstCondition() {

                public void accept(AstConditionVisitor visitor) 
		throws ParserException {
                    visitor.visitOperatorEquals(equal, v, w);
                }

                /** for debug only */
                public String toString() {
                    return "[Condition(op):equal=" + equal + ",v=" + v + ",w=" + w + "]";
                }

            };
    }

    public AstCondition createNotFreeCondition(Location location, final Identifier v, final Identifier w) {
        return new AstCondition() {

                public void accept(AstConditionVisitor visitor) 
		throws ParserException {
                    visitor.visitNotFreeIn(v, w);
                }

                /** for debug only */
                public String toString() {
                    return "[Condition(not-free-in):v=" + v + ",w=" + w + "]";
                }

            };
    }

    public AstCondition createPureCondition(Location location, final Identifier v) {
        return new AstCondition() {

                public void accept(AstConditionVisitor visitor) 
		throws ParserException {
                    visitor.visitPure(v);
                }

                /** for debug only */
                public String toString() {
                    return "[Condition(pure):v=" + v + "]";
                }

            };
    }

    public AstCondition createStaticCondition(Location location, final Identifier v) {
        return new AstCondition() {

                public void accept(AstConditionVisitor visitor) 
		throws ParserException {
                    visitor.visitStatic(v);
                }

                /** for debug only */
                public String toString() {
                    return "[Condition(static):v=" + v + "]";
                }

            };
    }

    public AstCondition createStaticArgsCondition(Location location, final Identifier v) {
        return new AstCondition() {

                public void accept(AstConditionVisitor visitor) 
		throws ParserException {
                    visitor.visitStaticArgs(v);
                }

                /** for debug only */
                public String toString() {
                    return "[Condition(staticargs):v=" + v + "]";
                }

            };
    }

    public AstCondition createDynamicCondition(Location location, final Identifier v) {
        return new AstCondition() {

                public void accept(AstConditionVisitor visitor) 
		throws ParserException {
                    visitor.visitDynamic(v);
                }

                /** for debug only */
                public String toString() {
                    return "[Condition(dynamic):v=" + v + "]";
                }

            };
    }

    public AstCondition createAtomicCondition(Location location, final Identifier v) {
	return new AstCondition() {
		
		public void accept(AstConditionVisitor visitor) 
		throws ParserException {
		    visitor.visitAtomic(v);
		}

		/** for debug only */
		public String toString() {
		    return "[Condition(atomic):v=" + v + "]";
		}
	    };
    }

    public AstCondition createDerivedCondition(Location location, final Identifier v) {
        return new AstCondition() {

                public void accept(AstConditionVisitor visitor) 
		throws ParserException {
                    visitor.visitDerived(v);
                }

                /** for debug only */
                public String toString() {
                    return "[Condition(derived):v=" + v + "]";
                }

            };
    }

    public AstCondition createSkolemCondition(Location location, final Identifier v, final Identifier w) {
        return new AstCondition() {

                public void accept(AstConditionVisitor visitor) 
		throws ParserException {
                    visitor.visitSkolem(v, w);
                }

                /** for debug only */
                public String toString() {
                    return "[Condition(skolem):v=" + v + ",w=" + w + "]";
                }

            };
    }

    public AstCondition createMayUpdateCondition(Location location, final Identifier r, final Identifier f) {
	return new AstCondition() {
		
		public void accept(AstConditionVisitor visitor) 
		throws ParserException {
		    visitor.visitMayUpdate(true, r, f);
		}

		/** for debug only */
		public String toString() {
		    return "[Condition(mayUpdate):r=" + r + ",f=" + f + "]";
		}
	    };
    }

    public AstCondition createNotUpdateCondition(Location location, final Identifier r, final Identifier f) {
	return new AstCondition() {
		
		public void accept(AstConditionVisitor visitor) 
		throws ParserException {
		    visitor.visitMayUpdate(false, r, f);
		}

		/** for debug only */
		public String toString() {
		    return "[Condition(notUpdate):r=" + r + ",f=" + f + "]";
		}
	    };
    }

    public AstCondition createMayAccessCondition(Location location, final Identifier r, final Identifier f) {
	return new AstCondition() {
		
		public void accept(AstConditionVisitor visitor) 
		throws ParserException {
		    visitor.visitMayAccess(true, r, f);
		}

		/** for debug only */
		public String toString() {
		    return "[Condition(mayAccess):r=" + r + ",f=" + f + "]";
		}
	    };
    }

    public AstCondition createNotAccessCondition(Location location, final Identifier r, final Identifier f) {
	return new AstCondition() {
		
		public void accept(AstConditionVisitor visitor) 
		throws ParserException {
		    visitor.visitMayAccess(false, r, f);
		}

		/** for debug only */
		public String toString() {
		    return "[Condition(notAccess):r=" + r + ",f=" + f + "]";
		}
	    };
    }

    public AstGoal createReplaceGoal(Location location,
                                     final String name,
                                     final AstTerm term,
                                     final AstSequent addSequent,
                                     final AstTacletDeclaration[] addRules) {
        return new AstGoal(location) {

                public void accept(AstGoalVisitor visitor) 
		throws ParserException {
                    visitor.visitReplace(name, term, addSequent, addRules);
                }

                /** for debug only */
                public String toString() {
                    return "[AstGoal:term=" + term + "]";
                }

            };
    }

    public AstGoal createReplaceGoal(Location location,
                                     final String name,
                                     final AstSequent sequent,
                                     final AstSequent addSequent,
                                     final AstTacletDeclaration[] addRules) {
        return new AstGoal(location) {

                public void accept(AstGoalVisitor visitor) 
		throws ParserException {
                    visitor.visitReplace(name, sequent, addSequent, addRules);
                }

                /** for debug only */
                public String toString() {
                    return "[AstGoal:sequent=" + sequent + "]";
                }

            };
    }

    public AstGoal createReplaceGoal(Location location,
				     final String name,
				     final AstSequent sequent) {
	return new AstGoal(location) {

		public void accept(AstGoalVisitor visitor) 
		throws ParserException {
		    visitor.visitReplace(name, sequent);
		}
		
		/** for debug only */
		public String toString() {
		    return "[AstGoal:sequent=" + sequent + "]";
		}
	    };
    }

    public AstTacletModifier createTacletHeuristics(Location location, final Identifier[] ids) {
        return new AstTacletModifier(location) {

                public void accept(AstTacletModifierVisitor visitor) 
		throws ParserException {
                    visitor.visitHeuristics(ids);
                }

                /** for debug only */
                public String toString() {
                    return "[AstTacletModifier:heuristics=" + ArrayUtil.toString(ids) + "]";
                }

            };
    }

    public AstTacletModifier createTacletNonInteractiveModifier(Location location) {
        return new AstTacletModifier(location) {

                public void accept(AstTacletModifierVisitor visitor) 
		throws ParserException {
                    visitor.visitNonInteractive();
                }

                /** for debug only */
                public String toString() {
                    return "[AstTacletModifier:noninteractive]";
                }

            };
    }


    public AstTacletModifier createTacletDisplayNameModifier(Location location, final String displayName) {
        return new AstTacletModifier(location) {

                public void accept(AstTacletModifierVisitor visitor) 
		throws ParserException {
                    visitor.visitDisplayName(displayName);
                }

                /** for debug only */
                public String toString() {
                    return "[AstTacletModifier:recursive]";
                }

            };
    }

    public AstTacletModifier createTacletHelpTextModifier(Location location, final String helpText) {
        return new AstTacletModifier(location) {

                public void accept(AstTacletModifierVisitor visitor) 
		throws ParserException {
                    visitor.visitHelpText(helpText);
                }

                /** for debug only */
                public String toString() {
                    return "[AstTacletModifier:recursive]";
                }

            };
    }

    public AstTacletModifier createTacletSameUpdateLevelModifier(Location location) {
	return new AstTacletModifier(location) {

		public void accept(AstTacletModifierVisitor visitor) 
		throws ParserException {
		    visitor.visitSameUpdateLevel();
		}
		
		/** for debug only */
                public String toString() {
                    return "[AstTacletModifier:sameUpdateLevel]";
                }

	    };
    }

    public AstTacletModifier createTacletInSequentStateModifier(Location location) {
	return new AstTacletModifier(location) {

		public void accept(AstTacletModifierVisitor visitor) 
		throws ParserException {
		    visitor.visitInSequentState();
		}
		
		/** for debug only */
                public String toString() {
                    return "[AstTacletModifier:inSequentState]";
                }

	    };
    }


    /* --- terms for asm rules --- */

    public AstAsmRule createAsmSeq(final Location location,
				   final AstAsmRule rule1, final AstAsmRule rule2) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
                    return visitor.visitSeq(closure, rule1, rule2, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(seq):rule1=" + rule1 + ",rule2=" + rule2 + "]";
                }

            };
    }

    public AstAsmRule createAsmPar(final Location location,
				   final AstAsmRule rule1, final AstAsmRule rule2) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
                    return visitor.visitPar(closure, rule1, rule2, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(par):rule1=" + rule1 + ",rule2=" + rule2 + "]";
                }

            };
    }

    public AstAsmRule createAsmSkip(final Location location) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
                    return visitor.visitSkip(closure, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(skip)]";
                }

            };
    }

    public AstAsmRule createAsmAssign(final Location location,
				      final AstTerm lhs, final AstTerm rhs) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
                    return visitor.visitAssign(closure, lhs, rhs, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(assign):lhs=" + lhs + ",rhs=" + rhs + "]";
                }

            };
    }

    public AstAsmRule createAsmCall(final Location location,
				    final Identifier id, final AstTerm[] terms) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure) 
		throws ParserException {
                    return visitor.visitCall(closure, id, terms, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(call):id=" + id + ",terms=" + terms + "]";
                }

            };
    }

    public AstAsmRule createAsmIf(final Location location, final AstTerm formula,
                                  final AstAsmRule thenRule, final AstAsmRule elseRule) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
                    return visitor.visitIf(closure, formula, thenRule, elseRule, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(if):formula=" + formula + ",thenRule=" +
			thenRule + ",elseRule" + elseRule + "]";
                }

            };
    }

    public AstAsmRule createCondAsm(final Location location,
				    final AstTerm[] formulas,
				    final AstAsmRule[] thenRules,
				    final AstAsmRule otherwiseRule) {
	return new AstAsmRule (location) {
		
		public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
		    return visitor.visitCond(closure, formulas,
					     thenRules, otherwiseRule, location);
		}

		public String toString() {
		    return "[AstAsmRule(cond):formulas=" + ArrayUtil.toString(formulas)
			+ ";thenRules=" + ArrayUtil.toString(thenRules)
			+ ";otherwiseRule=" + otherwiseRule + "]";
		}
	    };
    }
    
    public AstAsmRule createAsmLet(final Location location, final Identifier var,
				   final Identifier sort,
                                   final AstTerm term, final AstAsmRule rule) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		    throws ParserException  {
                    return visitor.visitLet(closure, var, sort, term, rule, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(let):var=" + var + ",sort=" + sort
			+ ",term=" + term + ",rule=" + rule + "]";
                }

            };
    }

    public AstAsmRule createAsmForall(final Location location,
                                      final Identifier var,
                                      final Identifier sort,
                                      final AstTerm formula,
                                      final AstAsmRule rule) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
                    return visitor.visitForall(closure, var, sort, formula, rule, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(forall):var="
                        + var
                        + ",sort="
                        + sort
                        + ",formula="
                        + formula
                        + ",rule="
                        + rule
                        + "]";
                }

            };
    }

    public AstAsmRule createAsmTry(final Location location,
				   final AstAsmRule tryRule, final AstAsmRule elseRule) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
                    return visitor.visitTry(closure, tryRule, elseRule, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(try):tryRule=" + tryRule + ",elseRule=" + elseRule + "]";
                }

            };
    }

    public AstAsmRule createAsmVariable(final Location location, final Identifier id) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
                    return visitor.visitAsmVariable(closure, id, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(variable):id=" + id + "]";
                }

            };
    }

    public AstAsmRule createAsmSubstitution(final Location location,
                                            final Identifier var,
                                            final Identifier sort,
                                            final AstTerm subst,
                                            final AstAsmRule rule) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
                    return visitor.visitSubstitution(closure, var, sort, subst, rule, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(subst):var=" + var + ",sort=" + sort +
			",subst=" + subst + ",rule=" + rule + "]";
                }

            };
    }

    public AstAsmRule createAsmRuleMeta(final Location location,
					final Identifier id, final AstAsmRule rule) {
        return new AstAsmRule(location) {

                public Object accept(AstTermVisitor visitor, ParsingStack closure)
		throws ParserException {
                    return visitor.visitMeta(closure, id, rule, location);
                }

                /** for debug only */
                public String toString() {
                    return "[AstAsmRule(meta):id=" + id + ",rule=" + rule + "]";
                }

            };
    }

    /* --- declarations --- */

    
    public AstSinglePassDeclaration createPrimitiveSortDeclaration(Location location,
								   Identifier id, 
								   final boolean isGenericSort) {
        return new AstSinglePassDeclaration(location, id) {

                public void accept(AstDeclarationVisitor visitor) 
		throws ParserException {
                    visitor.visitPrimitiveSort(isGenericSort);
                }

                public String toString2() {
                    return ",primitive sort";
                }

            };
    }
    
    public AstSinglePassDeclaration createEnumeratedSortDeclaration(Location location,
								    Identifier id,
								    final Identifier[] consts) {
	return new AstSinglePassDeclaration(location, id) {
		
		public void accept(AstDeclarationVisitor visitor) 
		throws ParserException {
		    visitor.visitEnumeratedSort(consts);
		}

		public String toString2() {
		    return ",enumerated sort";
		}
	    };
    }

   //  public AstDeclaration createSynonymousSortDeclaration(Location location,
// 						   Identifier id,
// 						   final AstType typeRef) {
// 	return new AstDeclaration(location, id) {
		
// 		public void accept(AstDeclarationVisitor visitor) 
// 		throws ParserException {
// 		    visitor.visitSynonymousSort(typeRef);
// 		}

// 		public String toString2() {
// 		    return ", synonymous sort";
// 		}
// 	    };
//     }

    public AstSinglePassDeclaration createSchemaVariableDeclaration(Location location,
							  Identifier id,
							  final AstSchemaType type) {
        return new AstSinglePassDeclaration(location, id) {

                public void accept(AstDeclarationVisitor visitor) 
		throws ParserException {
                    visitor.visitSchemaVariable(type);
                }

                public String toString2() {
                    return ",type=" + type;
                }

            };
    }

    public AstSinglePassDeclaration createPredicateDeclaration(Location location,
						     Identifier id,
						     final AstType[] argTypes) {
        return new AstSinglePassDeclaration(location, id) {

                public void accept(AstDeclarationVisitor visitor) 
		throws ParserException {
                    visitor.visitPredicate((AstType[]) ArrayUtil.copy(argTypes));
                }

                public String toString2() {
                    return ",args=" + ArrayUtil.toString(argTypes);
                }

            };
    }

    public AstMultiPassDeclaration createDerivedPredicateDeclaration(Location location,
								     Identifier id, 
								     final AstParameter[] args,
								     final AstTerm formula) {
	return new AstMultiPassDeclaration(location, id) {

		private AstParameter[] params = (AstParameter[]) ArrayUtil.copy(args);
		
		public void acceptFirstPass(AstDeclarationVisitor visitor) 
		throws ParserException {
		    visitor.visitDerivedPredicateFirstPass(params);
		}

		public void acceptSecondPass(AstDeclarationVisitor visitor)
		throws ParserException {
		    visitor.visitDerivedPredicateSecondPass(formula);
		}

		public String toString2() {
		    return ",args=" + ArrayUtil.toString(args) + ",formula=" + formula;
		}
	    };
    }

    public AstSinglePassDeclaration createFunctionDeclaration(Location location,
							      Identifier id,
							      final AstType[] argTypes,
							      final AstType returnType,
							      final boolean dynamic) {
        return new AstSinglePassDeclaration(location, id) {

                public void accept(AstDeclarationVisitor visitor) 
		throws ParserException {
                    visitor.visitFunction((AstType[]) ArrayUtil.copy(argTypes), returnType, dynamic);
                }

                public String toString2() {
                    return ",args=" + ArrayUtil.toString(argTypes) + ",ret=" + returnType;
                }

            };
    }

    public AstMultiPassDeclaration createDerivedFunctionDeclaration(Location location,
								    Identifier id,
								    final AstParameter[] args,
								    final AstType returnType,
								    final AstTerm body){
	return new AstMultiPassDeclaration(location, id) {

		private AstParameter[] params = (AstParameter[]) ArrayUtil.copy(args);
		
		public void acceptFirstPass(AstDeclarationVisitor visitor) 
		throws ParserException {
		    visitor.visitDerivedFunctionFirstPass(params, returnType);
		}

		public void acceptSecondPass(AstDeclarationVisitor visitor)
		throws ParserException {
		    visitor.visitDerivedFunctionSecondPass(body);
		}

		public String toString2() {
		    return ",args=" + ArrayUtil.toString(args) + ",ret=" + returnType + ",body=" + body;
		}
	    };
    }

    public AstSinglePassDeclaration createAbstractAsmRuleDeclaration(Location location,
								     Identifier id) {
	return new AstSinglePassDeclaration(location, id) {
		
		public void accept(AstDeclarationVisitor visitor)
		throws ParserException {
		    visitor.visitAbstractAsmRule();
		}
		
		public String toString2() {
		    return "";
		}
	    };
    }

    public AstMultiPassDeclaration createNamedRuleDeclaration(Location location,
							      Identifier id,
							      final AstParameter[] args,
							      final AstAsmRule rule) {
        return new AstMultiPassDeclaration(location, id) {

		private AstParameter[] params = (AstParameter[]) ArrayUtil.copy(args);

                public void acceptFirstPass(AstDeclarationVisitor visitor) 
		throws ParserException {
                    visitor.visitNamedRuleFirstPass(params);
                }

		public void acceptSecondPass(AstDeclarationVisitor visitor)
		throws ParserException {
		    visitor.visitNamedRuleSecondPass(rule);
		}

                public String toString2() {
                    return ",named rule";
                }

            };
    }

    public AstSinglePassDeclaration createLemmaDeclaration(Location location,
							   Identifier id,
							   final AstParameter[] params,
							   final AstTerm phi) {
	return new AstSinglePassDeclaration(location, id) {

		public void accept(AstDeclarationVisitor visitor) 
		throws ParserException {
		    visitor.visitLemma(params, phi);
		}

		public String toString2() {
		    return ",lemma";
		}

	    };
    }

    public AstSinglePassDeclaration createRuleSetDeclaration(Location location, Identifier id) {
        return new AstSinglePassDeclaration(location, id) {

                public void accept(AstDeclarationVisitor visitor)
		    throws ParserException {
                    visitor.visitRuleSet();
                }

                public String toString2() {
                    return ",RuleSet";
                }

            };
    }

    public AstSinglePassDeclaration createMetaOperatorDeclaration(Location location, 
								  Identifier id) {
	return new AstSinglePassDeclaration(location, id) {
		
		public void accept(AstDeclarationVisitor visitor)
		    throws ParserException {
		    visitor.visitMetaOperator();
		}

		public String toString2() {
		    return ",MetaOp";
		}
	    };
    }

    
    /* --- export info --- */

    public AstExport createNoSymbolsAstExport() {
	return new AstExport(null) {

		public ExportInfo accept(AstExportVisitor visitor) throws ParserException {
		    return visitor.visitNoSymbolsExport();
		}

		public String toString() {
		    return "[AstExport:NoSymbols]";
		}

	    };
    }
    
    public AstExport createAllSymbolsAstExport(final Location location) {

	return new AstExport(location) {
	
		public ExportInfo accept(AstExportVisitor visitor) throws ParserException {
		    return visitor.visitAllSymbolsExport(location);
		}

		public String toString() {
		    return "[AstExport:AllSymbols]";
		}

	    };
    }

    public AstExport createSomeSymbolsAstExport(final Location location,
						final AstRestrictedSymbol[] symbs) {
	return new AstExport(location) {
		
		public ExportInfo accept(AstExportVisitor visitor) throws ParserException {
		    return visitor.visitSomeSymbolsExport(symbs, location);
		}

		public String toString() {
		    return "[AstExport:SomeSymbols:symbs=" + ArrayUtil.toString(symbs) + "]";
		}

	    };
    }

    /* --- import info --- */

    public AstImport createNoSymbolsAstImport(final Location location, 
					     final Identifier unit) {
	
	return new AstImport(location) {
		
		protected Name internAcceptFirstPass(AstImportVisitor visitor)
		    throws ParserException {
		    return visitor.visitImportFirstPass(unit, location);
		}
		
		public ImportInfo acceptSecondPass(AstImportVisitor visitor)
		    throws ParserException {
		    return visitor.visitNoSymbolsImport(unit, location);
		}

		public String toString() {
		    return "[AstImport:NoSymbols:unit=" + unit + "]";
		} 
	    };
    }

    public AstImport createAllSymbolsAstImport(final Location location, 
					      final Identifier unit) {
	return new AstImport(location) {
		
		protected Name internAcceptFirstPass(AstImportVisitor visitor)
		    throws ParserException {
		    return visitor.visitImportFirstPass(unit, location);
		}

		public ImportInfo acceptSecondPass(AstImportVisitor visitor)
		    throws ParserException {
		    return visitor.visitAllSymbolsImport(unit, location);
		}

		public String toString() {
		    return "[AstImport:AllSymbols:unit=" + unit + "]";
		} 
	    };
    }

    public AstImport createSomeSymbolsAstImport(final Location location,
					       final Identifier unit,
					       final AstRestrictedSymbol[] symbols) {
	return new AstImport(location) {
		
		protected Name internAcceptFirstPass(AstImportVisitor visitor)
		    throws ParserException {
		    return visitor.visitImportFirstPass(unit, location);
		}

		public ImportInfo acceptSecondPass(AstImportVisitor visitor)
		    throws ParserException {
		    return visitor.visitSomeSymbolsImport(unit, symbols, location);
		}

		public String toString() {
		    return "[AstImport:SomeSymbols:unit=" + unit +
			";symbols=" + ArrayUtil.toString(symbols) + "]";
		}
	    };
    }
    
    /* --- unit file --- */

    public AstUnit createAstUnit(Location location,
				 Identifier unit,
				 AstExport export,
				 AstImport[] imports,
				 AstUnitDeclarations decls) {
	return new AstUnit(location, unit, export, imports, decls);
    }

    /* --- proof --- */

    public AstProof createPropAstProof(Location location,
				       AstProofMeta meta,
				       AstTerm problem,
				       AstProofExpression[] plogs,
				       AstProofExpression pexpr) {
	return AstProof.createPropAstProof(location, meta, problem, plogs, pexpr);
    }
    
    public AstProof createAxiomAstProof(Location location,
					AstProofMeta meta,
					AstTerm problem) {
	return AstProof.createAxiomAstProof(location, meta, problem);
    }

    public AstProof createTruthAstProof(Location location,
					AstProofMeta meta,
					AstTerm problem) {
	return AstProof.createTruthAstProof(location, meta, problem);
    }

}
