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


import de.uka.ilkd.key.parser.Location;

/** Abstract factory for creating AST nodes. */

public interface AstFactory {

    /* --- type references --- */

    /** Primitive type */
    AstType createPrimitiveTypeRef(Location location, Identifier sort);

    /** Sequence type */
    AstType createSequenceTypeRef(Location location, Identifier sort);

    /** Asm type */
    AstType createAsmRuleTypeRef(Location location);

    /** Primitive schema type.*/
    AstSchemaType createSchemaTypeRef(Location location, PrimitiveSchemaType sort, boolean rigid);

    /** Composite schema type. */
    AstSchemaType createComposedSchemaTypeRef(Location location, AstType sort, boolean rigid);
    
    /** Variable schema type. */
    AstSchemaType createVariableSchemaTypeRef(Location location, AstType sort);

    /** Schema type for new depending variables (skolem functions). */
    AstSchemaType createDependingSchemaTypeRef(Location location, AstType sort);

    /* --- first order logic terms --- */

    /** Operator term. */
    AstTerm createTerm(Location location, AstOperator op, AstTerm[] terms);

    /** Big term (And Or) */
    AstTerm createBigTerm(Location location, AstOperator op,
			  Identifier sort, Identifier func, Identifier narity , AstTerm form);

    /** Quantifier term. If sort is null, then var is a schema variable */
    AstTerm createTerm(Location location, AstQuantifier q, Identifier var, Identifier sort, AstTerm term);

    /** Function or predicate term. */
    AstTerm createTerm(Location location, Identifier id, AstTerm[] terms);

    /** Substitution term. If sort is null, then var is a schema variable */
    AstTerm createSubstitutionTerm(Location location, Identifier var, Identifier sort,
				   AstTerm subst, AstTerm term, boolean waryEx, boolean waryAll);

    /** Function Operator in formula */
    AstTerm createFunctionTerm(Location location, Identifier id, AstTerm func, AstTerm form);

    /** Abbreviation. */
    AstTerm createAbbreviationTerm(Location location, Identifier name);

    /* --- sequences and sets --- */

    //AstTerm createSetTerm(Location location, AstTerm[] elems);

    AstTerm createSequenceTerm(Location location, Identifier basesort, AstTerm[] elems, AstTerm tail);

    /* --- dynamic logic --- */

    /** Box operator: <tt>[rule] term</tt>. */
    AstTerm createDlBox(Location location, AstAsmRule rule, AstTerm term, AstTerm step);

    /** Diamond operator: <tt>&lt;rule&gt; term</tt>. */
    AstTerm createDlDiamond(Location location, AstAsmRule rule, AstTerm term, AstTerm step);

    /* --- taclets --- */

    /** Taclet condition: The top level funtion symbol of the terms represented by v and w equal. */
    AstCondition createOperatorEqualsCondition(Location location, boolean equal, Identifier v, Identifier w);

    /** Taclet condition: The variable represented by v occurs not free in the term represented by w. */
    AstCondition createNotFreeCondition(Location location, Identifier v, Identifier w);

    /** Taclet condition. The term represented by the schema variable is pure. */
    AstCondition createPureCondition(Location location, Identifier v);

    /** Taclet condition. The term represented by the schema variable is static. */
    AstCondition createStaticCondition(Location location, Identifier v);

    /** Taclet condition. All subterms of the the term represented by the schema variable are static. */
    AstCondition createStaticArgsCondition(Location location, Identifier v);

    /** Taclet condition. The top level operator of the term represented by the schema variable is dynamic. */
    AstCondition createDynamicCondition(Location location, Identifier v);

    /** Taclet condition. The top level operator of the formula is a predicate */
    AstCondition createAtomicCondition(Location location, Identifier v);

    /** Taclet condition. The top level operator of the term represented by the schema variable is an asm named rull cale. */
    AstCondition createDerivedCondition(Location location, Identifier v);

    /** Taclet condition. New skolem symbol with meta variables occuring in second term. */
    AstCondition createSkolemCondition(Location location, Identifier v, Identifier w);

    /** Taclet condition. if a rule r may update function f */
    AstCondition createMayUpdateCondition(Location location, Identifier r, Identifier f);

    /** Taclet condition. if a rule cannot update function f */
    AstCondition createNotUpdateCondition(Location location, Identifier r, Identifier f);

    /** Taclet condition. if a rule r may access a function f */
    AstCondition createMayAccessCondition(Location location, Identifier r, Identifier f);

    /** Taclet condition. if a rule cannot access a function f*/
    AstCondition createNotAccessCondition(Location location, Identifier r, Identifier f);

    /** Replace goal. */
    AstGoal createReplaceGoal(Location location, String name, 
			      AstTerm term, AstSequent addSequent, 
			      AstTacletDeclaration[] addRules);

    /** Replace goal. */
    AstGoal createReplaceGoal(Location location,
                              String name,
                              AstSequent sequent,
                              AstSequent addSequent,
                              AstTacletDeclaration[] addRules);

    /** Replace goal for elseif */
    AstGoal createReplaceGoal(Location location,
			      String name,
			      AstSequent sequent);

    /** Taclet modifier: heuristics. */
    AstTacletModifier createTacletHeuristics(Location location, Identifier[] ids);

    /** Taclet modifier: non interactive. */
    AstTacletModifier createTacletNonInteractiveModifier(Location location);

    /** Taclet modifier: display name. */
    AstTacletModifier createTacletDisplayNameModifier(Location location, String displayName);

    /** Taclet modifier: help text. */
    AstTacletModifier createTacletHelpTextModifier(Location location, String helpText);

    /** Taclet modifier: same update level */
    AstTacletModifier createTacletSameUpdateLevelModifier(Location location);

    /** Taclet modifier: in sequent state */
    AstTacletModifier createTacletInSequentStateModifier(Location location);

    /* --- terms for asm rules --- */

    /** Sequential ASM rule: <tt>rule1 ; rule2</tt>. */
    AstAsmRule createAsmSeq(Location location, AstAsmRule rule1, AstAsmRule rule2);

    /** Parallel ASM rule: <tt>rule1 rule2</tt>. */
    AstAsmRule createAsmPar(Location location, AstAsmRule rule1, AstAsmRule rule2);

    /** ASM skip rule. */
    AstAsmRule createAsmSkip(Location location);

    /** ASM update rule: <tt>lhs := rhs</tt>. */
    AstAsmRule createAsmAssign(Location location, AstTerm lhs, AstTerm rhs);

    /** ASM named rule call: <tt>id(terms)</tt>. */
    AstAsmRule createAsmCall(Location location, Identifier id, AstTerm[] terms);

    /** ASM if rule: <tt>if formula then thenRule</tt>. */
    AstAsmRule createAsmIf(Location location, AstTerm formula, AstAsmRule thenRule, AstAsmRule elseRule);

    /** ASM cond rule: <tt>cond phi_1 then r_1 end ... phi_n then r_n end otherwise r end end</tt>. */
    AstAsmRule createCondAsm(Location location,
			     AstTerm[] formulas,
			     AstAsmRule[] thenRules,
			     AstAsmRule otherwiseRule);

    /** ASM let rule: <tt>let var:sort := term in rule</tt>. */
    AstAsmRule createAsmLet(Location location, Identifier var, Identifier sort, AstTerm term, AstAsmRule rule);

    /** ASM forall rule: <tt>forall var:sort with formula do rule</tt>. */
    AstAsmRule createAsmForall(Location location, Identifier var, Identifier sort, AstTerm formula, AstAsmRule rule);

    /** ASM try rule: <tt>try tryRule else elseRule</tt>. */
    AstAsmRule createAsmTry(Location location, AstAsmRule tryRule, AstAsmRule elseRule);

    /** ASM schema variable. */
    AstAsmRule createAsmVariable(Location location, Identifier id);

    /** ASM substitution: <tt>{var:sort = subst} term</tt>. */
    AstAsmRule createAsmSubstitution(Location location,
                                     Identifier var,
                                     Identifier sort,
                                     AstTerm subst,
                                     AstAsmRule rule);

    /** ASM meta operator: <tt>id(rule)</tt>. The meta operator has exactly one argument. */
    AstAsmRule createAsmRuleMeta(Location location, Identifier id, AstAsmRule rule);

    /* --- declarations --- */

    

    /** Primitive sort declaration. */
    AstSinglePassDeclaration createPrimitiveSortDeclaration(Location location,
							    Identifier id,
							    boolean isGenericSort);

    /** Enumeration sort declaration. */
    AstSinglePassDeclaration createEnumeratedSortDeclaration(Location location,
							     Identifier id,
							     Identifier[] consts);

    /** Create synonymous sort declaration */
    // AstDeclaration createSynonymousSortDeclaration(Location location,
// 						   Identifier id,
// 						   AstType typeRef);

    /** Schema variable declaration. */
    AstSinglePassDeclaration createSchemaVariableDeclaration(Location location,
							     Identifier id,
							     AstSchemaType type);

    /** Predicate declaration. */
    AstSinglePassDeclaration createPredicateDeclaration(Location location,
							Identifier id,
							AstType[] argTypes);

    /** Derived Predicate declaration */
    AstMultiPassDeclaration createDerivedPredicateDeclaration(Location location,
								 Identifier id,
								 AstParameter[] args,
								 AstTerm formula);

    /** Function declaration. */
    AstSinglePassDeclaration createFunctionDeclaration(Location location,
						       Identifier id,
						       AstType[] argTypes,
						       AstType returnType,
						       boolean dynamic);

    /** Function declaration. */
    AstMultiPassDeclaration createDerivedFunctionDeclaration(Location location,
								Identifier id,
								AstParameter[] args,
								AstType returnType,
								AstTerm body);
    
    /** Abstract ASM rules, pseudo-constants, used to proof PO for taclets */
    AstSinglePassDeclaration createAbstractAsmRuleDeclaration(Location location,
							      Identifier id);
    
    /** Named ASM rule (rule) declaration. */
    AstMultiPassDeclaration createNamedRuleDeclaration(Location location,
							  Identifier id,
							  AstParameter[] params,
							  AstAsmRule rule);
    
    /** Lemma declaration (lemma a proof may use.) */
    AstSinglePassDeclaration createLemmaDeclaration(Location location,
						    Identifier id,
						    AstParameter[] params,
						    AstTerm phi);

    /** Rule Set (used for strategies) */
    AstSinglePassDeclaration createRuleSetDeclaration(Location location,
						      Identifier id);

    /** meta operator, just the declaration of the name, 
     * to put it in the namespace.
     */
    AstSinglePassDeclaration createMetaOperatorDeclaration(Location location,
							   Identifier id);
    
    /* --- export info --- */
    
    /** the current unit exports no symbols att all to other units. */
    AstExport createNoSymbolsAstExport();

    /** the current unit exports all its symbols to other units. */
    AstExport createAllSymbolsAstExport(Location location);

    /** the current unit exports some symbols to other units; the
     * the other stay private.
     */
    AstExport createSomeSymbolsAstExport(Location location, AstRestrictedSymbol[] symbols);


    /* --- import info --- */

    /** importing another unit without the namespace */
    AstImport createNoSymbolsAstImport(Location location, Identifier unit);

    /** importing another unit with the complete namespace */
    AstImport createAllSymbolsAstImport(Location location, Identifier unit);

    /** importing another unit with some symbols from the namespace */
    AstImport createSomeSymbolsAstImport(Location location,
					Identifier unit, AstRestrictedSymbol[] symbols);
    
    /* --- unit file -- */
    AstUnit createAstUnit(Location location,
			  Identifier unit,
			  AstExport export,
			  AstImport[] imports,
			  AstUnitDeclarations decls);


    /* -- proof -- */

    /** ast proof for a proposition */
    AstProof createPropAstProof(Location location,
				AstProofMeta meta,
				AstTerm problem,
				AstProofExpression[] plogs,
				AstProofExpression pexpr);
    
    /** ast proof for an axiom */
    AstProof createAxiomAstProof(Location location,
				 AstProofMeta meta,
				 AstTerm problem);

    /** ast proof for a mathematical proof (e.g. arthmetic thruth,
     * bothersome to proof mechanically */
    AstProof createTruthAstProof(Location location,
				 AstProofMeta meta,
				 AstTerm problem);

    /** Constants for the big boolean operator */
    final int ALL_TYPE = 0;
    final int STATIC_TYPE = 1;
    final int DYNAMIC_TYPE = 2;

    final int ALL_PROPERTY = 0;
    final int ACCESS_PROPERTY = 1;
    final int UPDATE_PROPERTY = 2;
}
